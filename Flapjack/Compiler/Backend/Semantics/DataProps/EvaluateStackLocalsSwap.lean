module

public import Flapjack.Compiler.Backend.Semantics.DataProps.EvaluateResourceSwap
public import Flapjack.Compiler.Backend.Semantics.DataProps.ApplyAuxFields
public import Flapjack.Compiler.Backend.Semantics.DataProps.InitialStateLaws
public import Flapjack.Compiler.Backend.Semantics.DataProps.Jump
public import Flapjack.Misc.ClockWeightInduction

@[expose] public section

/-!
# Stack and locals-size replacement under data evaluation

Counterpart of `cakeml/compiler/backend/semantics/dataPropsScript.sml:929`
`evaluate_stack_and_locals_swap`, together with the consequences
`evaluate_stack_swap` (`:1421`), `evaluate_stack` (`:1466`) and
`evaluate_NONE_jump_exc` (`:1480`).

The step lemmas below are the induction's cases. Those that are not yet
covered by the assembled theorem are Flapjack infrastructure toward the port of
`evaluate_stack_and_locals_swap`; they carry no `@[hol]` tag of their own.
-/

namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.DataSem

/-- The stack-and-locals replacement property for one program and state: the
    evaluation outcome is preserved when the stack is replaced by a list of the
    same length and the locals size is replaced, with only the resource
    observations free. -/
private def StackLocalsSwapAt {C F : Type} (program : DataLang.Prog) (state : State C F) : Prop :=
  ∀ (res : Option (Result (List DataSem.Value) DataSem.Value)) (next : State C F),
    evaluate program state = (res, next) →
    match res with
    | some (.err (.abort .typeError)) => True
    | some (.err (.abort a)) =>
        next.stack = [] ∧
          ∀ (xs : List Stack) (lsz : Option Nat), state.stack.length = xs.length →
            ∃ lss sfs smx phl, evaluate program { state with stack := xs, localsSize := lsz } =
              (some (.err (.abort a)),
                { next with
                  localsSize := lss
                  safeForSpace := sfs
                  stackMax := smx
                  peakHeapLength := phl })
    | some (.err (.raise t)) =>
        ∃ s2, jumpExc state = some s2 ∧ s2.locals = next.locals ∧ s2.stack = next.stack ∧
          s2.handler = next.handler ∧
          ∀ (xs : List Stack) (s7 : State C F) (lsz : Option Nat),
            jumpExc { state with stack := xs, localsSize := lsz } = some s7 →
            state.stack.length = xs.length →
            ∃ lss sfs smx phl, evaluate program { state with stack := xs, localsSize := lsz } =
              (some (.err (.raise t)),
                { next with
                  stack := s7.stack
                  handler := s7.handler
                  locals := s7.locals
                  localsSize := lss
                  safeForSpace := sfs
                  stackMax := smx
                  peakHeapLength := phl })
    | _ =>
        next.stack = state.stack ∧ next.handler = state.handler ∧
          ∀ (xs : List Stack) (lsz : Option Nat), state.stack.length = xs.length →
            ∃ lss sfs smx phl, evaluate program { state with stack := xs, localsSize := lsz } =
              (res, { next with
                localsSize := lss
                stack := xs
                safeForSpace := sfs
                stackMax := smx
                peakHeapLength := phl })

/-- The `Skip` case. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem stackLocalsSwap_skip {C F : Type} (state : State C F) :
    StackLocalsSwapAt (.skip : DataLang.Prog) state := by
  intro res next run
  simp only [evaluate, Prod.mk.injEq] at run
  obtain ⟨rfl, rfl⟩ := run
  refine ⟨rfl, rfl, ?_⟩
  intro xs lsz len
  exact ⟨lsz, state.safeForSpace, state.stackMax, state.peakHeapLength, by simp [evaluate]⟩

/-- The `Move` case. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem stackLocalsSwap_move {C F : Type} (dest src : Nat) (state : State C F) :
    StackLocalsSwapAt (.move dest src) state := by
  intro res next run
  cases read : getVar src state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    trivial
  | some value =>
    simp only [evaluate, read, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨rfl, rfl, ?_⟩
    intro xs lsz len
    exact ⟨lsz, state.safeForSpace, state.stackMax, state.peakHeapLength,
      by simp [evaluate, read, setVar]⟩

/-- The `Tick` case. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem stackLocalsSwap_tick {C F : Type} (state : State C F) :
    StackLocalsSwapAt (.tick : DataLang.Prog) state := by
  intro res next run
  by_cases zero : state.clock = 0
  · simp only [evaluate, zero, timeoutError] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨?_, ?_⟩
    · simp [flushState]
    · intro xs lsz len
      exact ⟨some 0, state.safeForSpace, state.stackMax, state.peakHeapLength,
        by simp [evaluate, zero, timeoutError, flushState]⟩
  · simp only [evaluate, zero] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨rfl, rfl, ?_⟩
    intro xs lsz len
    exact ⟨lsz, state.safeForSpace, state.stackMax, state.peakHeapLength,
      by simp [evaluate, zero, decClock]⟩

/-- The `MakeSpace` case. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem stackLocalsSwap_makeSpace {C F : Type} (amount : Nat) (names : NumSet)
    (state : State C F) : StackLocalsSwapAt (.makeSpace amount names) state := by
  intro res next run
  cases cut : cutEnv names state.locals with
  | none =>
    simp only [evaluate, cut, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    trivial
  | some env =>
    simp only [evaluate, cut, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨rfl, rfl, ?_⟩
    intro xs lsz len
    let target := addSpace { state with locals := env, stack := xs, localsSize := lsz } amount
    refine ⟨lsz, target.safeForSpace, state.stackMax, target.peakHeapLength, ?_⟩
    simp only [evaluate, cut]
    rfl

/-- The `Raise` case. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem stackLocalsSwap_raise {C F : Type} (name : Nat) (state : State C F) :
    StackLocalsSwapAt (.raise name) state := by
  intro res next run
  cases read : getVar name state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    trivial
  | some value =>
    cases jump : jumpExc state with
    | none =>
      simp only [evaluate, read, jump, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      trivial
    | some jumped =>
      simp only [evaluate, read, jump, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨jumped, rfl, rfl, rfl, rfl, ?_⟩
      intro xs s7 lsz jumpedRun len
      refine ⟨s7.localsSize, s7.safeForSpace, s7.stackMax, s7.peakHeapLength, ?_⟩
      obtain ⟨_, n1, e1, ls1, xs1, _, jumpedEq⟩ := jumpExcImp state jumped jump
      obtain ⟨_, n2, e2, ls2, xs2, _, s7Eq⟩ := jumpExcImp _ s7 jumpedRun
      subst s7
      rw [jumpedEq]
      simp [evaluate, read, jumpedRun]

/-- The `Return` case. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem stackLocalsSwap_return {C F : Type} (names : List Nat) (state : State C F) :
    StackLocalsSwapAt (.return names) state := by
  intro res next run
  cases read : DataSem.getVars names state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    trivial
  | some values =>
    have hres : res = some (.val values) := by
      have h := congrArg Prod.fst run
      simpa [evaluate, DataSem.getVars, read] using h.symm
    have hnext : next = flushState false state := by
      have h := congrArg Prod.snd run
      simpa [evaluate, DataSem.getVars, read] using h.symm
    rw [hres, hnext]
    refine ⟨rfl, rfl, ?_⟩
    intro xs lsz len
    exact ⟨some 0, state.safeForSpace, state.stackMax, state.peakHeapLength,
      by simp [evaluate, read, flushState]⟩

/-- The `If` case. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem stackLocalsSwap_if {C F : Type} (name : Nat) (yes no : DataLang.Prog)
    (state : State C F) (yesIH : StackLocalsSwapAt yes state) (noIH : StackLocalsSwapAt no state) :
    StackLocalsSwapAt (.ifThenElse name yes no) state := by
  intro res next run
  cases read : getVar name state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    trivial
  | some value =>
    by_cases yesValue : isBool true value
    · have branch : evaluate yes state = (res, next) := by
        simpa [evaluate, read, yesValue] using run
      have := yesIH res next branch
      simpa [evaluate, read, yesValue] using this
    · by_cases noValue : isBool false value
      · have branch : evaluate no state = (res, next) := by
          simpa [evaluate, read, yesValue, noValue] using run
        have := noIH res next branch
        simpa [evaluate, read, yesValue, noValue] using this
      · simp only [evaluate, read, yesValue, noValue, typeError] at run
        obtain ⟨rfl, rfl⟩ := run
        trivial

/-- A sequential composition whose first half has stopped returns the first
    half's result. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem seq_some {C F : Type} (first second : DataLang.Prog) (state : State C F)
    (stopped : Result (List DataSem.Value) DataSem.Value) (next : State C F)
    (run : evaluate first state = (some stopped, next)) :
    evaluate (.seq first second) state = (some stopped, next) := by
  have bound : next.clock ≤ state.clock := evaluateClock first state (some stopped) next run
  simp only [evaluate, run, fixClock, Nat.min_eq_right bound]

/-- A sequential composition whose first half continues evaluates the second
    half at the first half's result state. Flapjack infrastructure toward the
    port of HOL `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem seq_none {C F : Type} (first second : DataLang.Prog) (state mid : State C F)
    (run : evaluate first state = (none, mid)) :
    evaluate (.seq first second) state = evaluate second mid := by
  have bound : mid.clock ≤ state.clock := by
    simpa only [run] using evaluate_clock_le first state
  simp only [evaluate, run, fixClock, Nat.min_eq_right bound]

/-- The `Seq` case. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem stackLocalsSwap_seq {C F : Type} (first second : DataLang.Prog)
    (state : State C F) (firstIH : StackLocalsSwapAt first state)
    (secondIH : ∀ mid : State C F, mid.clock ≤ state.clock → StackLocalsSwapAt second mid) :
    StackLocalsSwapAt (.seq first second) state := by
  intro res next run
  cases firstRun : evaluate first state with
  | mk outcome mid =>
    have midClock : mid.clock ≤ state.clock := by
      simpa only [firstRun] using evaluate_clock_le first state
    cases outcome with
    | some stopped =>
      have clamp : fixClock state (evaluate first state) = (some stopped, mid) := by
        rw [fixClock_evaluate, firstRun]
      have hres : res = some stopped := by
        have h := congrArg Prod.fst run
        simpa only [evaluate, clamp] using h.symm
      have hnext : next = mid := by
        have h := congrArg Prod.snd run
        simpa only [evaluate, clamp] using h.symm
      rw [hres, hnext]
      have firstArm := firstIH (some stopped) mid firstRun
      cases stopped with
      | val values =>
        obtain ⟨stackSame, handlerSame, hall⟩ := firstArm
        refine ⟨stackSame, handlerSame, ?_⟩
        intro xs lsz len
        obtain ⟨lss, sfs, smx, phl, targetRun⟩ := hall xs lsz len
        refine ⟨lss, sfs, smx, phl, ?_⟩
        rw [seq_some first second _ (.val values) _ targetRun]
      | err error =>
        cases error with
        | abort reason =>
          cases reason with
          | typeError => trivial
          | timeoutError =>
            obtain ⟨stackEmpty, hall⟩ := firstArm
            refine ⟨stackEmpty, ?_⟩
            intro xs lsz len
            obtain ⟨lss, sfs, smx, phl, targetRun⟩ := hall xs lsz len
            refine ⟨lss, sfs, smx, phl, ?_⟩
            rw [seq_some first second _ (.err (.abort .timeoutError)) _ targetRun]
          | ffiError event =>
            obtain ⟨stackEmpty, hall⟩ := firstArm
            refine ⟨stackEmpty, ?_⟩
            intro xs lsz len
            obtain ⟨lss, sfs, smx, phl, targetRun⟩ := hall xs lsz len
            refine ⟨lss, sfs, smx, phl, ?_⟩
            rw [seq_some first second _ (.err (.abort (.ffiError event))) _ targetRun]
        | raise value =>
          obtain ⟨s2, jump, localsEq, stackEq, handlerEq, hall⟩ := firstArm
          refine ⟨s2, jump, localsEq, stackEq, handlerEq, ?_⟩
          intro xs s7 lsz jumpedRun len
          obtain ⟨lss, sfs, smx, phl, targetRun⟩ := hall xs s7 lsz jumpedRun len
          refine ⟨lss, sfs, smx, phl, ?_⟩
          rw [seq_some first second _ (.err (.raise value)) _ targetRun]
    | none =>
      have secondRun : evaluate second mid = (res, next) := by
        have clamp : fixClock state (evaluate first state) = (none, mid) := by
          rw [fixClock_evaluate, firstRun]
        simpa only [evaluate, clamp] using run
      have secondArm := secondIH mid midClock res next secondRun
      have firstArm := firstIH none mid firstRun
      have midStack : mid.stack = state.stack := firstArm.1
      have midHandler : mid.handler = state.handler := firstArm.2.1
      have firstHall := firstArm.2.2
      cases res with
      | none =>
        obtain ⟨stackSame, handlerSame, secondHall⟩ := secondArm
        refine ⟨stackSame.trans midStack, handlerSame.trans midHandler, ?_⟩
        intro xs lsz len
        obtain ⟨lss1, sfs1, smx1, phl1, firstTarget⟩ := firstHall xs lsz len
        obtain ⟨lss2, sfs2, smx2, phl2, secondTarget⟩ :=
          secondHall xs lss1 (by rw [midStack]; exact len)
        obtain ⟨mx', safe', peak', moved⟩ :=
          evaluate_stackSafePeakSwap smx1 sfs1 _ _ _ phl1 second secondTarget
        refine ⟨lss2, safe', mx', peak', ?_⟩
        rw [seq_none first second _ _ firstTarget]
        exact moved
      | some result =>
        cases result with
        | val values =>
          obtain ⟨stackSame, handlerSame, secondHall⟩ := secondArm
          refine ⟨stackSame.trans midStack, handlerSame.trans midHandler, ?_⟩
          intro xs lsz len
          obtain ⟨lss1, sfs1, smx1, phl1, firstTarget⟩ := firstHall xs lsz len
          obtain ⟨lss2, sfs2, smx2, phl2, secondTarget⟩ :=
            secondHall xs lss1 (by rw [midStack]; exact len)
          obtain ⟨mx', safe', peak', moved⟩ :=
            evaluate_stackSafePeakSwap smx1 sfs1 _ _ _ phl1 second secondTarget
          refine ⟨lss2, safe', mx', peak', ?_⟩
          rw [seq_none first second _ _ firstTarget]
          exact moved
        | err error =>
          cases error with
          | abort reason =>
            cases reason with
            | typeError => trivial
            | timeoutError =>
              obtain ⟨stackEmpty, secondHall⟩ := secondArm
              refine ⟨stackEmpty, ?_⟩
              intro xs lsz len
              obtain ⟨lss1, sfs1, smx1, phl1, firstTarget⟩ := firstHall xs lsz len
              obtain ⟨lss2, sfs2, smx2, phl2, secondTarget⟩ :=
                secondHall xs lss1 (by rw [midStack]; exact len)
              obtain ⟨mx', safe', peak', moved⟩ :=
                evaluate_stackSafePeakSwap smx1 sfs1 _ _ _ phl1 second secondTarget
              refine ⟨lss2, safe', mx', peak', ?_⟩
              rw [seq_none first second _ _ firstTarget]
              exact moved
            | ffiError event =>
              obtain ⟨stackEmpty, secondHall⟩ := secondArm
              refine ⟨stackEmpty, ?_⟩
              intro xs lsz len
              obtain ⟨lss1, sfs1, smx1, phl1, firstTarget⟩ := firstHall xs lsz len
              obtain ⟨lss2, sfs2, smx2, phl2, secondTarget⟩ :=
                secondHall xs lss1 (by rw [midStack]; exact len)
              obtain ⟨mx', safe', peak', moved⟩ :=
                evaluate_stackSafePeakSwap smx1 sfs1 _ _ _ phl1 second secondTarget
              refine ⟨lss2, safe', mx', peak', ?_⟩
              rw [seq_none first second _ _ firstTarget]
              exact moved
          | raise value =>
            obtain ⟨s2, jump, localsEq, stackEq, handlerEq, secondHall⟩ := secondArm
            have jumpState := jumpExc_transport mid state s2 midStack.symm midHandler.symm jump
            refine ⟨{ state with
                      stack := s2.stack
                      handler := s2.handler
                      locals := s2.locals
                      localsSize := s2.localsSize }, jumpState, ?_, ?_, ?_, ?_⟩
            · simpa using localsEq
            · simpa using stackEq
            · simpa using handlerEq
            · intro xs s7 lsz jumpedRun len
              have swappedJump := jumpExc_transport
                { state with stack := xs, localsSize := lsz }
                { mid with stack := xs, localsSize := lsz }
                s7 rfl (by simp only [midHandler]) jumpedRun
              obtain ⟨lss1, sfs1, smx1, phl1, firstTarget⟩ := firstHall xs lsz len
              obtain ⟨lss2, sfs2, smx2, phl2, secondTarget⟩ :=
                secondHall xs _ lss1 swappedJump (by rw [midStack]; exact len)
              obtain ⟨mx', safe', peak', moved⟩ :=
                evaluate_stackSafePeakSwap smx1 sfs1 _ _ _ phl1 second secondTarget
              refine ⟨lss2, safe', mx', peak', ?_⟩
              rw [seq_none first second _ _ firstTarget]
              exact moved

/-- Decrementing the clock commutes with the stack-and-locals update. Flapjack
    infrastructure toward the port of HOL `evaluate_stack_and_locals_swap`;
    no separate HOL original. -/
private theorem decClock_swapStackLocals {C F : Type} (state : State C F) (xs : List Stack)
    (lsz : Option Nat) :
    DataSem.decClock { state with stack := xs, localsSize := lsz } =
      { DataSem.decClock state with stack := xs, localsSize := lsz } := rfl

/-- Entering a call replaces the locals and the locals size but keeps the stack,
    so a stack-and-locals update passes through it with only the stack maximum
    and the safety observation free. Flapjack infrastructure toward the port of
    HOL `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem callEnv_swapStackLocals {C F : Type} (args : List DataSem.Value)
    (size : Option Nat) (state : State C F) (xs : List Stack) (lsz : Option Nat) :
    ∃ smx sfs, DataSem.callEnv args size { state with stack := xs, localsSize := lsz } =
      { DataSem.callEnv args size state with
        stack := xs
        stackMax := smx
        safeForSpace := sfs } := by
  unfold DataSem.callEnv
  exact ⟨_, _, rfl⟩

/-- Pushing an environment frame prepends it to the current stack and builds it
    from the current locals size, so a stack-and-locals update passes through it
    with only the stack maximum and the safety observation free. Flapjack
    infrastructure toward the port of HOL `evaluate_stack_and_locals_swap`;
    no separate HOL original. -/
private theorem pushEnv_false_swapStackLocals {C F : Type} (env : Spt DataSem.Value)
    (state : State C F) (xs : List Stack) (lsz : Option Nat) :
    ∃ smx sfs, DataSem.pushEnv env false { state with stack := xs, localsSize := lsz } =
      { DataSem.pushEnv env false state with
        stack := Stack.env lsz env :: xs
        localsSize := lsz
        stackMax := smx
        safeForSpace := sfs } := by
  unfold DataSem.pushEnv
  exact ⟨_, _, rfl⟩

/-- Restoring a saved environment commutes with the stack-and-locals update when
    the frames agree. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem popEnv_swapStackLocals {C F : Type} (state : State C F) (frame : Stack)
    (xs : List Stack) (lsz : Option Nat) :
    DataSem.popEnv { state with stack := frame :: xs, localsSize := lsz } =
      (DataSem.popEnv { state with stack := frame :: state.stack }).map
        (fun next => { next with stack := xs }) := by
  cases frame <;> simp [DataSem.popEnv]

/-- Raising past the saved exception frame depends only on the handler index
    and the stack, so two states that agree there produce jump results that
    agree in the locals, stack and handler they install. Flapjack
    infrastructure toward the port of HOL `evaluate_stack_and_locals_swap`;
    no separate HOL original. -/
private theorem jumpExc_agree {C F : Type} (left right : State C F)
    (sameStack : left.stack = right.stack) (sameHandler : left.handler = right.handler)
    (next : State C F) (run : jumpExc left = some next) :
    ∃ next', jumpExc right = some next' ∧ next'.locals = next.locals ∧
      next'.stack = next.stack ∧ next'.handler = next.handler := by
  unfold jumpExc at run ⊢
  rw [← sameStack, ← sameHandler] at ⊢
  by_cases guard : left.handler < left.stack.length
  · rw [if_pos guard] at run ⊢
    cases drop : left.stack.drop (left.stack.length - (left.handler + 1)) with
    | nil =>
      simp only [drop] at run
      cases run
    | cons frame rest =>
      cases frame with
      | env size env' =>
        simp only [drop] at run
        cases run
      | exc size env' handler =>
        simp only [drop, Option.some.injEq] at run
        subst next
        exact ⟨_, rfl, rfl, rfl, rfl⟩
  · rw [if_neg guard] at run
    simp at run

/-- The `Force` case with a tail call. Flapjack infrastructure toward the port
    of HOL `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem stackLocalsSwap_tailForce {C F : Type} (label src : Nat) (state : State C F)
    (bodyIH : ∀ (body : DataLang.Prog) (called : State C F),
      called.clock < state.clock → StackLocalsSwapAt body called) :
    StackLocalsSwapAt (.force none label src) state := by
  intro res next run
  cases read : getVar src state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    trivial
  | some thunk =>
    cases th : destThunk thunk state.refs with
    | badRef =>
      simp only [evaluate, read, th, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      trivial
    | notThunk =>
      simp only [evaluate, read, th, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      trivial
    | isThunk mode value =>
      cases mode with
      | evaluated =>
        simp only [evaluate, read, th, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨rfl, rfl, ?_⟩
        intro xs lsz len
        exact ⟨some 0, state.safeForSpace, state.stackMax, state.peakHeapLength,
          by simp [evaluate, read, th, flushState]⟩
      | notEvaluated =>
        cases found : findCode (some label) [thunk, value] state.code state.stackFrameSizes with
        | none =>
          simp only [evaluate, read, th, found, typeError, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          trivial
        | some entry =>
          obtain ⟨args, body, size⟩ := entry
          by_cases zero : state.clock = 0
          · simp only [evaluate, read, th, found, zero, timeoutError] at run
            obtain ⟨rfl, rfl⟩ := run
            refine ⟨?_, ?_⟩
            · simp
            · intro xs lsz len
              exact ⟨lsz, state.safeForSpace, state.stackMax, state.peakHeapLength,
                by simp [evaluate, read, th, found, zero]⟩
          · let called := DataSem.callEnv args size (DataSem.decClock state)
            have clockLt : called.clock < state.clock := by
              simp only [called, DataSem.callEnv, DataSem.decClock]
              omega
            have calledStack : called.stack = state.stack := rfl
            have calledHandler : called.handler = state.handler := rfl
            cases bodyRun : evaluate body called with
            | mk outcome last =>
              simp only [evaluate, read, th, found, zero, if_false] at run ⊢
              simp only [called] at bodyRun
              rw [bodyRun] at run
              cases outcome with
              | none =>
                obtain ⟨rfl, rfl⟩ := run
                trivial
              | some outcome =>
                cases outcome with
                | val values =>
                  obtain ⟨rfl, rfl⟩ := run
                  have bodyArm := bodyIH body called clockLt (some (.val values)) last bodyRun
                  obtain ⟨lastStack, lastHandler, bodyHall⟩ := bodyArm
                  refine ⟨lastStack.trans calledStack.symm,
                    lastHandler.trans calledHandler.symm, ?_⟩
                  intro xs lsz len
                  obtain ⟨lss, sfs, smx, phl, bodyTarget⟩ :=
                    bodyHall xs size (by
                      rw [calledStack]
                      exact len)
                  obtain ⟨callMax, callSafe, callEq⟩ :=
                    callEnv_swapStackLocals args size (DataSem.decClock state) xs lsz
                  obtain ⟨mx', safe', peak', moved⟩ :=
                    evaluate_stackSafePeakSwap callMax callSafe _ _ _ state.peakHeapLength body
                      bodyTarget
                  refine ⟨lss, safe', mx', peak', ?_⟩
                  have bridge :
                      DataSem.callEnv args size
                          (DataSem.decClock { state with stack := xs, localsSize := lsz }) =
                        { { called with stack := xs, localsSize := size } with
                          stackMax := callMax
                          safeForSpace := callSafe
                          peakHeapLength := state.peakHeapLength } := by
                    rw [decClock_swapStackLocals, callEq]
                    rfl
                  rw [bridge, moved]
                | err error =>
                  cases error with
                  | abort a =>
                    cases a with
                    | typeError =>
                      obtain ⟨rfl, rfl⟩ := run
                      trivial
                    | timeoutError =>
                      obtain ⟨rfl, rfl⟩ := run
                      have bodyArm :
                          last.stack = [] ∧
                            ∀ (xs : List Stack) (lsz : Option Nat),
                              called.stack.length = xs.length →
                              ∃ lss sfs smx phl, evaluate body { called with
                                  stack := xs, localsSize := lsz } =
                                (some (.err (.abort .timeoutError)),
                                  { last with
                                    localsSize := lss
                                    safeForSpace := sfs
                                    stackMax := smx
                                    peakHeapLength := phl }) :=
                        bodyIH body called clockLt (some (.err (.abort .timeoutError))) last bodyRun
                      obtain ⟨lastEmpty, bodyHall⟩ := bodyArm
                      refine ⟨lastEmpty, ?_⟩
                      intro xs lsz len
                      obtain ⟨lss, sfs, smx, phl, bodyTarget⟩ :=
                        bodyHall xs size (by
                          rw [calledStack]
                          exact len)
                      obtain ⟨callMax, callSafe, callEq⟩ :=
                        callEnv_swapStackLocals args size (DataSem.decClock state) xs lsz
                      obtain ⟨mx', safe', peak', moved⟩ :=
                        evaluate_stackSafePeakSwap callMax callSafe _ _ _ state.peakHeapLength body
                          bodyTarget
                      refine ⟨lss, safe', mx', peak', ?_⟩
                      have bridge :
                          DataSem.callEnv args size
                              (DataSem.decClock { state with stack := xs, localsSize := lsz }) =
                            { { called with stack := xs, localsSize := size } with
                              stackMax := callMax
                              safeForSpace := callSafe
                              peakHeapLength := state.peakHeapLength } := by
                        rw [decClock_swapStackLocals, callEq]
                        rfl
                      rw [bridge, moved]
                    | ffiError event =>
                      obtain ⟨rfl, rfl⟩ := run
                      have bodyArm :
                          last.stack = [] ∧
                            ∀ (xs : List Stack) (lsz : Option Nat),
                              called.stack.length = xs.length →
                              ∃ lss sfs smx phl, evaluate body { called with
                                  stack := xs, localsSize := lsz } =
                                (some (.err (.abort (.ffiError event))),
                                  { last with
                                    localsSize := lss
                                    safeForSpace := sfs
                                    stackMax := smx
                                    peakHeapLength := phl }) :=
                        bodyIH body called clockLt (some (.err (.abort (.ffiError event))))
                          last bodyRun
                      obtain ⟨lastEmpty, bodyHall⟩ := bodyArm
                      refine ⟨lastEmpty, ?_⟩
                      intro xs lsz len
                      obtain ⟨lss, sfs, smx, phl, bodyTarget⟩ :=
                        bodyHall xs size (by
                          rw [calledStack]
                          exact len)
                      obtain ⟨callMax, callSafe, callEq⟩ :=
                        callEnv_swapStackLocals args size (DataSem.decClock state) xs lsz
                      obtain ⟨mx', safe', peak', moved⟩ :=
                        evaluate_stackSafePeakSwap callMax callSafe _ _ _ state.peakHeapLength body
                          bodyTarget
                      refine ⟨lss, safe', mx', peak', ?_⟩
                      have bridge :
                          DataSem.callEnv args size
                              (DataSem.decClock { state with stack := xs, localsSize := lsz }) =
                            { { called with stack := xs, localsSize := size } with
                              stackMax := callMax
                              safeForSpace := callSafe
                              peakHeapLength := state.peakHeapLength } := by
                        rw [decClock_swapStackLocals, callEq]
                        rfl
                      rw [bridge, moved]
                  | raise t =>
                    obtain ⟨rfl, rfl⟩ := run
                    have bodyArm :
                        ∃ s2, jumpExc called = some s2 ∧ s2.locals = last.locals ∧
                          s2.stack = last.stack ∧ s2.handler = last.handler ∧
                          ∀ (xs : List Stack) (s7 : State C F) (lsz : Option Nat),
                            jumpExc { called with stack := xs, localsSize := lsz } = some s7 →
                            called.stack.length = xs.length →
                            ∃ lss sfs smx phl, evaluate body { called with
                                stack := xs, localsSize := lsz } =
                              (some (.err (.raise t)),
                                { last with
                                  stack := s7.stack
                                  handler := s7.handler
                                  locals := s7.locals
                                  localsSize := lss
                                  safeForSpace := sfs
                                  stackMax := smx
                                  peakHeapLength := phl }) :=
                      bodyIH body called clockLt (some (.err (.raise t))) last bodyRun
                    obtain ⟨s2, jumped, localsEq, stackEq, handlerEq, bodyHall⟩ := bodyArm
                    obtain ⟨s3, jumpedState, locals3, stack3, handler3⟩ :=
                      jumpExc_agree called state rfl rfl s2 jumped
                    refine ⟨s3, jumpedState, locals3.trans localsEq,
                      stack3.trans stackEq, handler3.trans handlerEq, ?_⟩
                    intro xs s7 lsz jumpedRun len
                    obtain ⟨s7', jumpedRun', locals7, stack7, handler7⟩ :=
                      jumpExc_agree { state with stack := xs, localsSize := lsz }
                        { called with stack := xs, localsSize := size } rfl rfl s7 jumpedRun
                    obtain ⟨lss, sfs, smx, phl, bodyTarget⟩ :=
                      bodyHall xs s7' size jumpedRun' (by
                        rw [calledStack]
                        exact len)
                    obtain ⟨callMax, callSafe, callEq⟩ :=
                      callEnv_swapStackLocals args size (DataSem.decClock state) xs lsz
                    obtain ⟨mx', safe', peak', moved⟩ :=
                      evaluate_stackSafePeakSwap callMax callSafe _ _ _ state.peakHeapLength body
                        bodyTarget
                    refine ⟨lss, safe', mx', peak', ?_⟩
                    have bridge :
                        DataSem.callEnv args size
                            (DataSem.decClock { state with stack := xs, localsSize := lsz }) =
                          { { called with stack := xs, localsSize := size } with
                            stackMax := callMax
                            safeForSpace := callSafe
                            peakHeapLength := state.peakHeapLength } := by
                      rw [decClock_swapStackLocals, callEq]
                      rfl
                    rw [bridge, moved, locals7, stack7, handler7]

/-- Prepending a frame does not change the frames counted back from the top when
    the index stays inside the original stack. Flapjack infrastructure toward
    the port of HOL `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem wordSemLastN_cons {α : Type} (n : Nat) (a : α) (l : List α)
    (bound : n < l.length) :
    wordSemLastN (n + 1) (a :: l) = wordSemLastN (n + 1) l := by
  rw [wordSemLastN_eq_drop, wordSemLastN_eq_drop]
  simp only [List.length_cons]
  have step : l.length + 1 - (n + 1) = (l.length - (n + 1)) + 1 := by omega
  rw [step, List.drop_succ_cons]

/-- Prepending an environment frame leaves the exception search unchanged, so a
    successful jump through the longer stack succeeds through the original one
    with the same control fields. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem jumpExc_envFrame {C F : Type} (state : State C F) (size : Option Nat)
    (env : Spt DataSem.Value) (next : State C F)
    (run : jumpExc { state with stack := Stack.env size env :: state.stack } = some next) :
    ∃ next', jumpExc state = some next' ∧ next'.locals = next.locals ∧
      next'.stack = next.stack ∧ next'.handler = next.handler := by
  obtain ⟨bound, n, e, ls, xs, lastN, nextEq⟩ :=
    jumpExcImp { state with stack := Stack.env size env :: state.stack } next run
  have bound' : state.handler < state.stack.length + 1 := by
    simpa using bound
  have lastN' : wordSemLastN (state.handler + 1) (Stack.env size env :: state.stack) =
      .exc ls e n :: xs := by
    simpa using lastN
  have inside : state.handler < state.stack.length := by
    by_contra notInside
    rw [not_lt] at notInside
    have sameLen : state.handler = state.stack.length := by omega
    rw [sameLen, wordSemLastN_eq_drop] at lastN'
    simp only [List.length_cons] at lastN'
    rw [show state.stack.length + 1 - (state.stack.length + 1) = 0 from by omega,
      List.drop_zero] at lastN'
    cases lastN'
  have dropEq :
      state.stack.drop (state.stack.length - (state.handler + 1)) = .exc ls e n :: xs := by
    rw [← wordSemLastN_eq_drop]
    rw [← wordSemLastN_cons state.handler (Stack.env size env) state.stack (by omega)]
    exact lastN'
  refine ⟨{ state with handler := n, locals := e, stack := xs, localsSize := ls }, ?_, ?_, ?_, ?_⟩
  · unfold jumpExc
    rw [if_pos inside, dropEq]
  · rw [nextEq]
  · rw [nextEq]
  · rw [nextEq]

/-- A successful jump through the original stack also succeeds through the same
    stack with an environment frame on top, with the same control fields.
    Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem jumpExc_prepend {C F : Type} (state : State C F) (size : Option Nat)
    (env : Spt DataSem.Value) (next : State C F) (run : jumpExc state = some next) :
    ∃ next', jumpExc { state with stack := Stack.env size env :: state.stack } = some next' ∧
      next'.locals = next.locals ∧ next'.stack = next.stack ∧ next'.handler = next.handler := by
  obtain ⟨inside, n, e, ls, xs, lastN, nextEq⟩ := jumpExcImp state next run
  have lastN' : wordSemLastN (state.handler + 1) (Stack.env size env :: state.stack) =
      .exc ls e n :: xs := by
    rw [wordSemLastN_cons state.handler (Stack.env size env) state.stack inside]
    exact lastN
  have dropEq : (Stack.env size env :: state.stack).drop
      ((Stack.env size env :: state.stack).length - (state.handler + 1)) = .exc ls e n :: xs := by
    rw [← wordSemLastN_eq_drop]
    exact lastN'
  have guard : state.handler < (Stack.env size env :: state.stack).length := by
    simp only [List.length_cons]
    omega
  refine ⟨{ { state with stack := Stack.env size env :: state.stack } with
      handler := n
      locals := e
      stack := xs
      localsSize := ls }, ?_, ?_, ?_, ?_⟩
  · unfold jumpExc
    rw [if_pos guard, dropEq]
  · rw [nextEq]
  · rw [nextEq]
  · rw [nextEq]

/-- A jump in the source state reaches the same frame through a call state whose
    stack carries one extra environment frame. Flapjack infrastructure toward the
    port of HOL `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem jumpExc_prependCall {C F : Type} (state called : State C F)
    (size : Option Nat) (env : Spt DataSem.Value)
    (sameStack : called.stack = Stack.env size env :: state.stack)
    (sameHandler : called.handler = state.handler)
    (next : State C F) (run : jumpExc state = some next) :
    ∃ next', jumpExc called = some next' ∧ next'.locals = next.locals ∧
      next'.stack = next.stack ∧ next'.handler = next.handler := by
  obtain ⟨middle, middleRun, localsM, stackM, handlerM⟩ := jumpExc_prepend state size env next run
  have framedStack :
      ({ state with stack := Stack.env size env :: state.stack } : State C F).stack =
        called.stack := by
    simp only [sameStack]
  have framedHandler :
      ({ state with stack := Stack.env size env :: state.stack } : State C F).handler =
        called.handler := by
    simp only [sameHandler]
  have transported :=
    jumpExc_transport { state with stack := Stack.env size env :: state.stack } called middle
      framedStack.symm framedHandler.symm middleRun
  refine ⟨_, transported, ?_, ?_, ?_⟩
  · simp only [localsM]
  · simp only [stackM]
  · simp only [handlerM]

/-- A jump in a call state whose stack carries one extra environment frame reaches
    the same frame in the source state. Flapjack infrastructure toward the port of
    HOL `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem jumpExc_callToState {C F : Type} (state called : State C F)
    (size : Option Nat) (env : Spt DataSem.Value)
    (sameStack : called.stack = Stack.env size env :: state.stack)
    (sameHandler : called.handler = state.handler)
    (next : State C F) (run : jumpExc called = some next) :
    ∃ next', jumpExc state = some next' ∧ next'.locals = next.locals ∧
      next'.stack = next.stack ∧ next'.handler = next.handler := by
  have framedStack :
      ({ state with stack := Stack.env size env :: state.stack } : State C F).stack =
        called.stack := by
    simp only [sameStack]
  have framedHandler :
      ({ state with stack := Stack.env size env :: state.stack } : State C F).handler =
        called.handler := by
    simp only [sameHandler]
  have transported :=
    jumpExc_transport called { state with stack := Stack.env size env :: state.stack } next
      framedStack framedHandler run
  obtain ⟨next', nextRun, locals', stack', handler'⟩ :=
    jumpExc_envFrame state size env _ transported
  exact ⟨next', nextRun, locals', stack', handler'⟩

/-- Restoring an environment frame prepends nothing and keeps the handler, so the
    popped state keeps the stack tail and the handler. Flapjack infrastructure
    toward the port of HOL `evaluate_stack_and_locals_swap`; no separate HOL
    original. -/
private theorem popEnv_env_some {C F : Type} (state : State C F) (size : Option Nat)
    (env : Spt DataSem.Value) (rest : List Stack)
    (stackEq : state.stack = Stack.env size env :: rest) :
    popEnv state = some { state with locals := env, stack := rest, localsSize := size } := by
  simp only [DataSem.popEnv, stackEq]

/-- The `Force` case with a returning call. Flapjack infrastructure toward the
    port of HOL `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem stackLocalsSwap_returningForce {C F : Type} (dest : Nat) (live : NumSet)
    (label src : Nat) (state : State C F)
    (bodyIH : ∀ (body : DataLang.Prog) (called : State C F),
      called.clock < state.clock → StackLocalsSwapAt body called) :
    StackLocalsSwapAt (.force (some (dest, live)) label src) state := by
  intro res next run
  cases read : getVar src state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    trivial
  | some thunk =>
    cases th : destThunk thunk state.refs with
    | badRef =>
      simp only [evaluate, read, th, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      trivial
    | notThunk =>
      simp only [evaluate, read, th, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      trivial
    | isThunk mode value =>
      cases mode with
      | evaluated =>
        cases cut : cutEnv live state.locals with
        | none =>
          simp only [evaluate, read, th, cut, typeError, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          trivial
        | some env =>
          simp only [evaluate, read, th, cut, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨rfl, rfl, ?_⟩
          intro xs lsz len
          exact ⟨lsz, state.safeForSpace, state.stackMax, state.peakHeapLength,
            by simp [evaluate, read, th, cut, setVar]⟩
      | notEvaluated =>
        cases found : findCode (some label) [thunk, value] state.code state.stackFrameSizes with
        | none =>
          simp only [evaluate, read, th, found, typeError, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          trivial
        | some entry =>
          obtain ⟨args, body, size⟩ := entry
          cases cut : cutEnv live state.locals with
          | none =>
            simp only [evaluate, read, th, found, cut, typeError, Prod.mk.injEq] at run
            obtain ⟨rfl, rfl⟩ := run
            trivial
          | some env =>
            by_cases zero : state.clock = 0
            · simp only [evaluate, read, th, found, cut, zero, timeoutError] at run
              obtain ⟨rfl, rfl⟩ := run
              refine ⟨?_, ?_⟩
              · simp
              · intro xs lsz len
                let targetCall :=
                  DataSem.callEnv args size
                    (DataSem.pushEnv env false
                      (DataSem.decClock { state with stack := xs, localsSize := lsz }))
                refine ⟨size, targetCall.safeForSpace, targetCall.stackMax,
                  state.peakHeapLength, ?_⟩
                simp only [evaluate, read, th, found, cut, zero, reduceIte]
                simp only [targetCall, zero, DataSem.callEnv, DataSem.pushEnv,
                  DataSem.decClock, reduceIte, Bool.false_eq_true]
                rfl
            · let callState :=
                DataSem.callEnv args size (DataSem.pushEnv env false (DataSem.decClock state))
              have clockLt : callState.clock < state.clock := by
                simp only [callState, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock]
                omega
              have callStack :
                  callState.stack = Stack.env state.localsSize env :: state.stack := rfl
              have callHandler : callState.handler = state.handler := rfl
              cases bodyRun : evaluate body callState with
              | mk outcome last =>
                simp only [evaluate, read, th, found, cut, zero, if_false] at run ⊢
                simp only [callState] at bodyRun
                rw [bodyRun] at run
                simp only [fixClock] at run ⊢
                cases outcome with
                | none =>
                  obtain ⟨rfl, rfl⟩ := run
                  trivial
                | some outcome =>
                  cases outcome with
                  | val values =>
                    cases values with
                    | nil =>
                      obtain ⟨rfl, rfl⟩ := run
                      trivial
                    | cons value rest =>
                      cases rest with
                      | cons other tail =>
                        obtain ⟨rfl, rfl⟩ := run
                        trivial
                      | nil =>
                        have bodyArm :=
                          bodyIH body callState clockLt (some (.val [value])) last bodyRun
                        obtain ⟨lastStack, lastHandler, bodyHall⟩ := bodyArm
                        have clampedStack :
                            ({ last with clock := min callState.clock last.clock } :
                              State C F).stack
                              = Stack.env state.localsSize env :: state.stack := by
                          simp only [lastStack, callStack]
                        have clampedHandler :
                            ({ last with clock := min callState.clock last.clock } :
                              State C F).handler = state.handler := by
                          simp only [lastHandler, callHandler]
                        have poppedEq :=
                          popEnv_env_some { last with clock := min callState.clock last.clock }
                            state.localsSize env state.stack clampedStack
                        rw [poppedEq] at run
                        obtain ⟨rfl, rfl⟩ := run
                        refine ⟨?_, ?_, ?_⟩
                        · simp only [setVar]
                        · simp only [setVar, clampedHandler]
                        · intro xs lsz len
                          obtain ⟨lss, sfs, smx, phl, bodyTarget⟩ :=
                            bodyHall (Stack.env lsz env :: xs) size (by
                              simp only [callStack, List.length_cons, len])
                          let targetCall :=
                            DataSem.callEnv args size
                              (DataSem.pushEnv env false
                                (DataSem.decClock { state with stack := xs, localsSize := lsz }))
                          have targetEq : targetCall =
                              DataSem.callEnv args size
                                (DataSem.pushEnv env false
                                  (DataSem.decClock { state with
                                    stack := xs
                                    localsSize := lsz })) := rfl
                          obtain ⟨mx', safe', peak', moved⟩ :=
                            evaluate_stackSafePeakSwap targetCall.stackMax targetCall.safeForSpace
                              _ _ _ targetCall.peakHeapLength body bodyTarget
                          have bridge : targetCall =
                              { { callState with
                                  stack := Stack.env lsz env :: xs
                                  localsSize := size } with
                                stackMax := targetCall.stackMax
                                safeForSpace := targetCall.safeForSpace
                                peakHeapLength := targetCall.peakHeapLength } := rfl
                          let movedState : State C F :=
                            { { last with
                                localsSize := lss
                                stack := Stack.env lsz env :: xs
                                safeForSpace := sfs
                                stackMax := smx
                                peakHeapLength := phl } with
                              stackMax := mx'
                              safeForSpace := safe'
                              peakHeapLength := peak' }
                          let targetClamped : State C F :=
                            { movedState with clock := min targetCall.clock movedState.clock }
                          have targetStack : targetClamped.stack = Stack.env lsz env :: xs := rfl
                          have targetPopped := popEnv_env_some targetClamped lsz env xs targetStack
                          refine ⟨lsz, safe', mx', peak', ?_⟩
                          rw [← targetEq, bridge, moved]
                          have clockEq : min callState.clock last.clock =
                              min targetCall.clock movedState.clock := rfl
                          simp only [clockEq]
                          rfl
                  | err error =>
                    cases error with
                    | abort a =>
                      cases a with
                      | typeError =>
                        obtain ⟨rfl, rfl⟩ := run
                        trivial
                      | timeoutError =>
                        obtain ⟨rfl, rfl⟩ := run
                        have bodyArm :
                            last.stack = [] ∧
                              ∀ (xs : List Stack) (lsz : Option Nat),
                                callState.stack.length = xs.length →
                                ∃ lss sfs smx phl, evaluate body { callState with
                                    stack := xs, localsSize := lsz } =
                                  (some (.err (.abort .timeoutError)),
                                    { last with
                                      localsSize := lss
                                      safeForSpace := sfs
                                      stackMax := smx
                                      peakHeapLength := phl }) :=
                          bodyIH body callState clockLt (some (.err (.abort .timeoutError)))
                            last bodyRun
                        obtain ⟨lastEmpty, bodyHall⟩ := bodyArm
                        refine ⟨lastEmpty, ?_⟩
                        intro xs lsz len
                        obtain ⟨lss, sfs, smx, phl, bodyTarget⟩ :=
                          bodyHall (Stack.env lsz env :: xs) size (by
                            simp only [callStack, List.length_cons, len])
                        let targetCall :=
                          DataSem.callEnv args size
                            (DataSem.pushEnv env false
                              (DataSem.decClock { state with stack := xs, localsSize := lsz }))
                        have targetEq : targetCall =
                            DataSem.callEnv args size
                              (DataSem.pushEnv env false
                                (DataSem.decClock { state with
                                  stack := xs
                                  localsSize := lsz })) := rfl
                        obtain ⟨mx', safe', peak', moved⟩ :=
                          evaluate_stackSafePeakSwap targetCall.stackMax targetCall.safeForSpace
                            _ _ _ targetCall.peakHeapLength body bodyTarget
                        have bridge : targetCall =
                            { { callState with
                                stack := Stack.env lsz env :: xs
                                localsSize := size } with
                              stackMax := targetCall.stackMax
                              safeForSpace := targetCall.safeForSpace
                              peakHeapLength := targetCall.peakHeapLength } := rfl
                        refine ⟨lss, safe', mx', peak', ?_⟩
                        rw [← targetEq, bridge, moved]
                      | ffiError event =>
                        obtain ⟨rfl, rfl⟩ := run
                        have bodyArm :
                            last.stack = [] ∧
                              ∀ (xs : List Stack) (lsz : Option Nat),
                                callState.stack.length = xs.length →
                                ∃ lss sfs smx phl, evaluate body { callState with
                                    stack := xs, localsSize := lsz } =
                                  (some (.err (.abort (.ffiError event))),
                                    { last with
                                      localsSize := lss
                                      safeForSpace := sfs
                                      stackMax := smx
                                      peakHeapLength := phl }) :=
                          bodyIH body callState clockLt (some (.err (.abort (.ffiError event))))
                            last bodyRun
                        obtain ⟨lastEmpty, bodyHall⟩ := bodyArm
                        refine ⟨lastEmpty, ?_⟩
                        intro xs lsz len
                        obtain ⟨lss, sfs, smx, phl, bodyTarget⟩ :=
                          bodyHall (Stack.env lsz env :: xs) size (by
                            simp only [callStack, List.length_cons, len])
                        let targetCall :=
                          DataSem.callEnv args size
                            (DataSem.pushEnv env false
                              (DataSem.decClock { state with stack := xs, localsSize := lsz }))
                        have targetEq : targetCall =
                            DataSem.callEnv args size
                              (DataSem.pushEnv env false
                                (DataSem.decClock { state with
                                  stack := xs
                                  localsSize := lsz })) := rfl
                        obtain ⟨mx', safe', peak', moved⟩ :=
                          evaluate_stackSafePeakSwap targetCall.stackMax targetCall.safeForSpace
                            _ _ _ targetCall.peakHeapLength body bodyTarget
                        have bridge : targetCall =
                            { { callState with
                                stack := Stack.env lsz env :: xs
                                localsSize := size } with
                              stackMax := targetCall.stackMax
                              safeForSpace := targetCall.safeForSpace
                              peakHeapLength := targetCall.peakHeapLength } := rfl
                        refine ⟨lss, safe', mx', peak', ?_⟩
                        rw [← targetEq, bridge, moved]
                    | raise t =>
                      obtain ⟨rfl, rfl⟩ := run
                      have bodyArm :
                          ∃ s2, jumpExc callState = some s2 ∧ s2.locals = last.locals ∧
                            s2.stack = last.stack ∧ s2.handler = last.handler ∧
                            ∀ (xs : List Stack) (s7 : State C F) (lsz : Option Nat),
                              jumpExc { callState with stack := xs, localsSize := lsz } = some s7 →
                              callState.stack.length = xs.length →
                              ∃ lss sfs smx phl, evaluate body { callState with
                                  stack := xs, localsSize := lsz } =
                                (some (.err (.raise t)),
                                  { last with
                                    stack := s7.stack
                                    handler := s7.handler
                                    locals := s7.locals
                                    localsSize := lss
                                    safeForSpace := sfs
                                    stackMax := smx
                                    peakHeapLength := phl }) :=
                        bodyIH body callState clockLt (some (.err (.raise t))) last bodyRun
                      obtain ⟨s2, jumped, localsEq, stackEq, handlerEq, bodyHall⟩ := bodyArm
                      obtain ⟨s3, jumpedState, locals3, stack3, handler3⟩ :=
                        jumpExc_callToState state callState state.localsSize env callStack
                          callHandler s2 jumped
                      have clampedLocals :
                          ({ last with clock := min callState.clock last.clock } :
                            State C F).locals = s3.locals := by
                        simp only [locals3, localsEq]
                      have clampedStack :
                          ({ last with clock := min callState.clock last.clock } :
                            State C F).stack = s3.stack := by
                        simp only [stack3, stackEq]
                      have clampedHandler :
                          ({ last with clock := min callState.clock last.clock } :
                            State C F).handler = s3.handler := by
                        simp only [handler3, handlerEq]
                      refine ⟨s3, jumpedState, clampedLocals.symm, clampedStack.symm,
                        clampedHandler.symm, ?_⟩
                      intro xs s7 lsz jumpedRun len
                      obtain ⟨s7', jumpedRun', locals7, stack7, handler7⟩ :=
                        jumpExc_prependCall { state with stack := xs, localsSize := lsz }
                          { callState with
                            stack := Stack.env lsz env :: xs
                            localsSize := size } lsz env rfl rfl s7 jumpedRun
                      obtain ⟨lss, sfs, smx, phl, bodyTarget⟩ :=
                        bodyHall (Stack.env lsz env :: xs) s7' size jumpedRun' (by
                          rw [callStack]
                          simp only [List.length_cons, len])
                      let targetCall :=
                        DataSem.callEnv args size
                          (DataSem.pushEnv env false
                            (DataSem.decClock { state with stack := xs, localsSize := lsz }))
                      have targetEq : targetCall =
                          DataSem.callEnv args size
                            (DataSem.pushEnv env false
                              (DataSem.decClock { state with
                                stack := xs
                                localsSize := lsz })) := rfl
                      obtain ⟨mx', safe', peak', moved⟩ :=
                        evaluate_stackSafePeakSwap targetCall.stackMax targetCall.safeForSpace
                          _ _ _ targetCall.peakHeapLength body bodyTarget
                      have bridge : targetCall =
                          { { callState with
                              stack := Stack.env lsz env :: xs
                              localsSize := size } with
                            stackMax := targetCall.stackMax
                            safeForSpace := targetCall.safeForSpace
                            peakHeapLength := targetCall.peakHeapLength } := rfl
                      refine ⟨lss, safe', mx', peak', ?_⟩
                      rw [← targetEq, bridge, moved]
                      simp only [locals7, stack7, handler7]
                      rfl

/-- Reserving space reads only the reserved amount. Flapjack infrastructure
    toward the port of HOL `evaluate_stack_and_locals_swap`; no separate HOL
    original. -/
private theorem consumeSpace_swapStackLocals {C F : Type} (amount : Nat) (state : State C F)
    (xs : List Stack) (lsz : Option Nat) :
    consumeSpace amount { state with stack := xs, localsSize := lsz } =
      (consumeSpace amount state).map
        (fun next => { next with stack := xs, localsSize := lsz }) := by
  simp only [consumeSpace]
  split <;> simp_all

/-- Space accounting at a stack-and-locals-swapped state. Flapjack
    infrastructure toward the port of HOL `evaluate_stack_and_locals_swap`;
    no separate HOL original. -/
private theorem doSpace_swapStackLocals {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value)
    (state : State C F) (xs : List Stack) (lsz : Option Nat) (next : State C F)
    (run : doSpace op values state = some next) :
    ∃ sfs phl, doSpace op values { state with stack := xs, localsSize := lsz } =
      some { next with
        stack := xs
        localsSize := lsz
        safeForSpace := sfs
        peakHeapLength := phl } := by
  by_cases reset : DataLang.opSpaceReset op
  · rw [doSpaceAlt, if_pos reset] at run ⊢
    cases run
    exact ⟨_, _, rfl⟩
  · rw [doSpaceAlt, if_neg reset] at run ⊢
    cases consume : consumeSpace (DataSpace.opSpaceReq op values.length) state with
    | none =>
      simp only [consume] at run
      simp at run
    | some consumed =>
      simp only [consume] at run
      cases run
      have swap := consumeSpace_swapStackLocals (DataSpace.opSpaceReq op values.length) state xs lsz
      simp only [consume, Option.map_some] at swap
      exact ⟨_, _, swap⟩

/-- Space accounting fails at a stack-and-locals-swapped state exactly when it
    fails at the original. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem doSpace_swapStackLocals_none {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (xs : List Stack) (lsz : Option Nat)
    (run : doSpace op values state = none) :
    doSpace op values { state with stack := xs, localsSize := lsz } = none := by
  by_cases reset : DataLang.opSpaceReset op
  · rw [doSpaceAlt, if_pos reset] at run
    simp at run
  · rw [doSpaceAlt, if_neg reset] at run ⊢
    cases consume : consumeSpace (DataSpace.opSpaceReq op values.length) state with
    | none =>
      have swap := consumeSpace_swapStackLocals (DataSpace.opSpaceReq op values.length) state xs lsz
      simp only [consume, Option.map_none] at swap
      exact swap
    | some consumed =>
      simp only [consume] at run
      simp at run

/-- The limit check at a stack-and-locals-swapped state. Flapjack
    infrastructure toward the port of HOL `evaluate_stack_and_locals_swap`;
    no separate HOL original. -/
private theorem doLimSafe_swapStackLocals {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value)
    (state : State C F) (xs : List Stack) (lsz : Option Nat) :
    doLimSafe { state with stack := xs, localsSize := lsz } op values =
      { doLimSafe state op values with stack := xs, localsSize := lsz } := by
  simp [doLimSafe]

/-- Stack accounting at a stack-and-locals-swapped state. Flapjack
    infrastructure toward the port of HOL `evaluate_stack_and_locals_swap`;
    no separate HOL original. -/
private theorem doStack_swapStackLocals {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value)
    (state : State C F) (xs : List Stack) (lsz : Option Nat) :
    ∃ smx sfs, doStack op values { state with stack := xs, localsSize := lsz } =
      { doStack op values state with
        stack := xs
        localsSize := lsz
        safeForSpace := sfs
        stackMax := smx } := by
  unfold doStack
  exact ⟨_, _, rfl⟩

end Flapjack.Compiler.Backend.DataProps
