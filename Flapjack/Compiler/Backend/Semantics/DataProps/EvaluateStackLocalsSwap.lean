module

public import Flapjack.Compiler.Backend.Semantics.DataProps.EvaluateResourceSwap
public import Flapjack.Compiler.Backend.Semantics.DataProps.AppWithLocals
public import Flapjack.Compiler.Backend.Semantics.DataProps.ApplyAuxFields
public import Flapjack.Compiler.Backend.Semantics.DataProps.ApplyConst
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
          secondHall xs lss1 (by
            rw [midStack]
            exact len)
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
            secondHall xs lss1 (by
              rw [midStack]
              exact len)
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
                secondHall xs lss1 (by
                  rw [midStack]
                  exact len)
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
                secondHall xs lss1 (by
                  rw [midStack]
                  exact len)
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
                secondHall xs _ lss1 swappedJump (by
                  rw [midStack]
                  exact len)
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

/-- The `Call` case with a tail call. Flapjack infrastructure toward the port of
    HOL `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem stackLocalsSwap_tailCall {C F : Type} (dest : Option Nat) (names : List Nat)
    (handler : Option (Nat × DataLang.Prog)) (state : State C F)
    (bodyIH : ∀ (body : DataLang.Prog) (called : State C F),
      called.clock < state.clock → StackLocalsSwapAt body called) :
    StackLocalsSwapAt (.call none dest names handler) state := by
  intro res next run
  cases read : DataSem.getVars names state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    trivial
  | some values =>
    cases found : findCode dest values state.code state.stackFrameSizes with
    | none =>
      simp only [evaluate, read, found, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      trivial
    | some entry =>
      obtain ⟨args, body, size⟩ := entry
      cases handler with
      | some handled =>
        simp only [evaluate, read, found, Option.isSome_some, if_true, typeError,
          Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        trivial
      | none =>
        by_cases zero : state.clock = 0
        · simp only [evaluate, read, found, Option.isSome_none, Bool.false_eq_true, if_false,
            zero, if_true, timeoutError, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨?_, ?_⟩
          · simp [flushState]
          · intro xs lsz len
            exact ⟨some 0, state.safeForSpace, state.stackMax, state.peakHeapLength,
              by simp [evaluate, read, found, zero, flushState]⟩
        · let called := DataSem.callEnv args size (DataSem.decClock state)
          have clockLt : called.clock < state.clock := by
            simp only [called, DataSem.callEnv, DataSem.decClock]
            omega
          have calledStack : called.stack = state.stack := rfl
          have calledHandler : called.handler = state.handler := rfl
          cases bodyRun : evaluate body called with
          | mk outcome last =>
            simp only [evaluate, read, found, Option.isSome_none, Bool.false_eq_true, if_false,
              zero, if_false] at run ⊢
            simp only [called] at bodyRun
            rw [bodyRun] at run
            cases outcome with
            | none =>
              obtain ⟨rfl, rfl⟩ := run
              trivial
            | some outcome =>
              cases outcome with
              | val values' =>
                obtain ⟨rfl, rfl⟩ := run
                have bodyArm := bodyIH body called clockLt (some (.val values')) last bodyRun
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
                      { { called with
                          stack := xs
                          localsSize := size } with
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
                          { { called with
                              stack := xs
                              localsSize := size } with
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
                          { { called with
                              stack := xs
                              localsSize := size } with
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
                  refine ⟨s3, jumpedState, locals3.trans localsEq, stack3.trans stackEq,
                    handler3.trans handlerEq, ?_⟩
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
                        { { called with
                            stack := xs
                            localsSize := size } with
                          stackMax := callMax
                          safeForSpace := callSafe
                          peakHeapLength := state.peakHeapLength } := by
                    rw [decClock_swapStackLocals, callEq]
                    rfl
                  rw [bridge, moved, locals7, stack7, handler7]

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

/-- Pushing a frame of either kind prepends it to the current stack, keeps the
    locals size and builds the frame from the current locals size, so a
    stack-and-locals update passes through it with only the stack maximum and
    the safety observation free. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem pushEnv_swapStackLocals {C F : Type} (env : Spt DataSem.Value) (handler : Bool)
    (state : State C F) (xs : List Stack) (lsz : Option Nat) :
    DataSem.pushEnv env handler { state with stack := xs, localsSize := lsz } =
      { DataSem.pushEnv env handler state with
        stack := (if handler then Stack.exc lsz env state.handler else Stack.env lsz env) :: xs
        localsSize := lsz
        handler := if handler then xs.length else state.handler
        stackMax :=
          (DataSem.pushEnv env handler { state with
            stack := xs
            localsSize := lsz }).stackMax
        safeForSpace :=
          (DataSem.pushEnv env handler { state with
            stack := xs
            localsSize := lsz }).safeForSpace } := by
  unfold DataSem.pushEnv
  cases handler <;> rfl

/-- Restoring an exception frame installs its saved handler along with its locals
    and stack tail. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem popEnv_exc_some {C F : Type} (state : State C F) (size : Option Nat)
    (env : Spt DataSem.Value) (saved : Nat) (rest : List Stack)
    (stackEq : state.stack = Stack.exc size env saved :: rest) :
    popEnv state =
      some { state with
        locals := env
        stack := rest
        localsSize := size
        handler := saved } := by
  simp only [DataSem.popEnv, stackEq]

/-- Restoring an environment frame prepends nothing and keeps the handler, so the
    popped state keeps the stack tail and the handler. Flapjack infrastructure
    toward the port of HOL `evaluate_stack_and_locals_swap`; no separate HOL
    original. -/
private theorem popEnv_env_some {C F : Type} (state : State C F) (size : Option Nat)
    (env : Spt DataSem.Value) (rest : List Stack)
    (stackEq : state.stack = Stack.env size env :: rest) :
    popEnv state = some { state with locals := env, stack := rest, localsSize := size } := by
  simp only [DataSem.popEnv, stackEq]

/-- A jump from a state whose stack starts with an exception frame and whose
    handler counts the frames below it unwinds to that frame's saved handler,
    environment and size. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem jumpExc_excHead {C F : Type} (state : State C F) (size : Option Nat)
    (env : Spt DataSem.Value) (saved : Nat) (rest : List Stack)
    (stackEq : state.stack = Stack.exc size env saved :: rest)
    (handlerEq : state.handler = rest.length) :
    jumpExc state =
      some { state with
        handler := saved
        locals := env
        stack := rest
        localsSize := size } := by
  unfold DataSem.jumpExc
  rw [stackEq, handlerEq]
  simp only [List.length_cons]
  rw [if_pos (by omega)]
  simp only [Nat.sub_self, List.drop_zero]

/-- Restoring the frame that a call pushed keeps the stack tail and installs
    the saved environment, the caller's locals size and its handler. The
    handler observation depends on the frame kind. Flapjack infrastructure
    toward the port of HOL `evaluate_stack_and_locals_swap`; no separate HOL
    original. -/
private theorem popEnv_pushedFrame {C F : Type} (handler : Option (Nat × DataLang.Prog))
    (source frameState : State C F) (env : Spt DataSem.Value) (lsz : Option Nat)
    (rest : List Stack)
    (stackEq : frameState.stack =
      (if handler.isSome then Stack.exc lsz env source.handler else Stack.env lsz env) :: rest) :
    popEnv frameState = some { frameState with
      locals := env
      stack := rest
      localsSize := lsz
      handler := if handler.isSome then source.handler else frameState.handler } := by
  cases handler with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, if_false] at stackEq
    exact popEnv_env_some frameState lsz env rest stackEq
  | some entry =>
    simp only [Option.isSome_some, if_true] at stackEq
    exact popEnv_exc_some frameState lsz env source.handler rest stackEq

/-- The callee of a returning call, evaluated at the stack-and-locals-swapped
    call state, raises the same exception and unwinds to the swapped stack with
    the saved environment. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem callBody_raiseTarget {C F : Type} (args : List DataSem.Value) (size : Option Nat)
    (env : Spt DataSem.Value) (handler : Option (Nat × DataLang.Prog)) (body : DataLang.Prog)
    (state callState last : State C F) (value : DataSem.Value) (xs : List Stack) (lsz : Option Nat)
    (callEq : callState = DataSem.callEnv args size
      (DataSem.pushEnv env handler.isSome (DataSem.decClock state)))
    (len : state.stack.length = xs.length)
    {s7 : State C F}
    (jumpedRun : jumpExc (DataSem.callEnv args size
        (DataSem.pushEnv env handler.isSome
          (DataSem.decClock { state with stack := xs, localsSize := lsz }))) = some s7)
    (s7Stack : s7.stack = xs) (s7Handler : s7.handler = state.handler) (s7Locals : s7.locals = env)
    (bodyHall : ∀ (xs' : List Stack) (s7' : State C F) (lsz' : Option Nat),
      jumpExc { callState with stack := xs', localsSize := lsz' } = some s7' →
      callState.stack.length = xs'.length →
      ∃ lss sfs smx phl, evaluate body { callState with stack := xs', localsSize := lsz' } =
        (some (.err (.raise value)),
          { last with
            stack := s7'.stack
            handler := s7'.handler
            locals := s7'.locals
            localsSize := lss
            safeForSpace := sfs
            stackMax := smx
            peakHeapLength := phl })) :
    ∃ lss sfs smx phl, evaluate body
        (DataSem.callEnv args size
          (DataSem.pushEnv env handler.isSome
            (DataSem.decClock { state with stack := xs, localsSize := lsz }))) =
      (some (.err (.raise value)),
        { last with
          stack := xs
          handler := state.handler
          locals := env
          localsSize := lss
          safeForSpace := sfs
          stackMax := smx
          peakHeapLength := phl }) := by
  let frame : Stack :=
    if handler.isSome then Stack.exc lsz env state.handler else Stack.env lsz env
  let targetCall := DataSem.callEnv args size
    (DataSem.pushEnv env handler.isSome
      (DataSem.decClock { state with stack := xs, localsSize := lsz }))
  let callFrame : State C F := { callState with stack := frame :: xs, localsSize := size }
  have targetStack : targetCall.stack = frame :: xs := rfl
  have callFrameStack : callFrame.stack = targetCall.stack := rfl
  have callFrameHandler : callFrame.handler = targetCall.handler := by
    have lhs : callFrame.handler =
        if handler.isSome then state.stack.length else state.handler := by
      show callState.handler = _
      rw [callEq]
      rfl
    have rhs : targetCall.handler =
        if handler.isSome then xs.length else state.handler := rfl
    rw [lhs, rhs, len]
  have jumpedAt : jumpExc callFrame = some { callFrame with
      stack := s7.stack
      handler := s7.handler
      locals := s7.locals
      localsSize := s7.localsSize } :=
    jumpExc_transport targetCall callFrame s7 callFrameStack callFrameHandler jumpedRun
  have callStack : callState.stack =
      (if handler.isSome then Stack.exc state.localsSize env state.handler
      else Stack.env state.localsSize env) :: state.stack := by
    rw [callEq]
    rfl
  obtain ⟨lss, sfs, smx, phl, bodyTarget⟩ :=
    bodyHall (frame :: xs)
      { callFrame with
        stack := s7.stack
        handler := s7.handler
        locals := s7.locals
        localsSize := s7.localsSize }
      size jumpedAt (by
        have callLen : callState.stack.length = state.stack.length + 1 := by
          rw [callStack]
          simp only [List.length_cons]
        have targetLen : (frame :: xs).length = xs.length + 1 := by
          simp only [List.length_cons]
        rw [callLen, targetLen, len])
  have controlStack : ({ callFrame with
      stack := s7.stack
      handler := s7.handler
      locals := s7.locals
      localsSize := s7.localsSize } : State C F).stack = xs := by
    simp only [s7Stack]
  have controlHandler : ({ callFrame with
      stack := s7.stack
      handler := s7.handler
      locals := s7.locals
      localsSize := s7.localsSize } : State C F).handler = state.handler := by
    simp only [s7Handler]
  have controlLocals : ({ callFrame with
      stack := s7.stack
      handler := s7.handler
      locals := s7.locals
      localsSize := s7.localsSize } : State C F).locals = env := by
    simp only [s7Locals]
  have bridge : targetCall =
      { callFrame with
        stackMax := targetCall.stackMax
        safeForSpace := targetCall.safeForSpace
        peakHeapLength := targetCall.peakHeapLength } := by
    have expand : targetCall =
        { callFrame with
          handler := targetCall.handler
          stackMax := targetCall.stackMax
          safeForSpace := targetCall.safeForSpace
          peakHeapLength := targetCall.peakHeapLength } := by
      dsimp only [targetCall, callFrame]
      rw [callEq]
      rfl
    rw [expand, ← callFrameHandler]
  obtain ⟨mx', safe', peak', moved⟩ :=
    evaluate_stackSafePeakSwap targetCall.stackMax targetCall.safeForSpace _ _ _
      targetCall.peakHeapLength body bodyTarget
  have targetEq : targetCall = DataSem.callEnv args size
      (DataSem.pushEnv env handler.isSome
        (DataSem.decClock { state with stack := xs, localsSize := lsz })) := rfl
  refine ⟨lss, safe', mx', peak', ?_⟩
  rw [← targetEq, bridge, moved, controlStack, controlHandler, controlLocals]

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

/-- The `Call` case with a returning frame and no handler. Flapjack
    infrastructure toward the port of HOL `evaluate_stack_and_locals_swap`;
    no separate HOL original. -/
private theorem stackLocalsSwap_returningCall_noHandler {C F : Type} (dest : Option Nat)
    (names : List Nat) (returns : List Nat) (live : NumSet) (state : State C F)
    (bodyIH : ∀ (body : DataLang.Prog) (called : State C F),
      called.clock < state.clock → StackLocalsSwapAt body called) :
    StackLocalsSwapAt (.call (some (returns, live)) dest names none) state := by
  intro res next run
  cases vars : DataSem.getVars names state.locals with
  | none =>
    simp only [evaluate, vars, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    trivial
  | some values =>
    cases found : findCode dest values state.code state.stackFrameSizes with
    | none =>
      simp only [evaluate, vars, found, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      trivial
    | some entry =>
      obtain ⟨args, body, size⟩ := entry
      by_cases distinct : returns.Nodup
      · cases cut : cutEnv live state.locals with
        | none =>
          simp only [evaluate, vars, found, distinct, cut, typeError] at run
          obtain ⟨rfl, rfl⟩ := run
          trivial
        | some env =>
          by_cases zero : state.clock = 0
          · simp only [evaluate, vars, found, distinct, cut, zero, timeoutError] at run
            obtain ⟨rfl, rfl⟩ := run
            refine ⟨?_, ?_⟩
            · simp
            · intro xs lsz len
              let targetCall := DataSem.callEnv args size
                (DataSem.pushEnv env false
                  (DataSem.decClock { state with stack := xs, localsSize := lsz }))
              refine ⟨size, targetCall.safeForSpace, targetCall.stackMax,
                targetCall.peakHeapLength, ?_⟩
              simp only [evaluate, vars, found, distinct, cut, zero, timeoutError]
              simp only [targetCall, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock,
                Option.isSome_none, Bool.false_eq_true, decide_true, Bool.not_true, if_true,
                if_false]
              rw [← zero]
          · let callState := DataSem.callEnv args size
              (DataSem.pushEnv env false (DataSem.decClock state))
            have clockLt : callState.clock < state.clock := by
              simp only [callState, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock]
              omega
            have callStack : callState.stack = Stack.env state.localsSize env :: state.stack := rfl
            have callHandler : callState.handler = state.handler := rfl
            cases bodyRun : evaluate body callState with
            | mk outcome last =>
              simp only [evaluate, vars, found, distinct, cut, zero, if_false,
                Option.isSome_none, Bool.false_eq_true, decide_true, Bool.not_true] at run ⊢
              simp only [callState] at bodyRun
              rw [bodyRun] at run
              simp only [fixClock] at run ⊢
              cases outcome with
              | none =>
                simp only [typeError, Prod.mk.injEq] at run
                obtain ⟨rfl, rfl⟩ := run
                trivial
              | some outcome =>
                cases outcome with
                | val results =>
                  by_cases length : results.length = returns.length
                  · revert run
                    cases popped : popEnv
                        { last with clock := min callState.clock last.clock } with
                    | none =>
                      intro run
                      simp only [length, typeError] at run
                      obtain ⟨rfl, rfl⟩ := run
                      trivial
                    | some final =>
                      intro run
                      have bodyArm :=
                        bodyIH body callState clockLt (some (.val results)) last bodyRun
                      obtain ⟨lastStack, lastHandler, bodyHall⟩ := bodyArm
                      have clampedStack :
                          ({ last with clock := min callState.clock last.clock } :
                            State C F).stack = Stack.env state.localsSize env :: state.stack := by
                        simp only [lastStack, callStack]
                      have poppedEq := popEnv_env_some
                        { last with clock := min callState.clock last.clock }
                        state.localsSize env state.stack clampedStack
                      have finalEq : final =
                          { { last with clock := min callState.clock last.clock } with
                            locals := env
                            stack := state.stack
                            localsSize := state.localsSize } := by
                        rw [poppedEq] at popped
                        injection popped with h
                        exact h.symm
                      rw [finalEq] at run
                      have resEq : res = none := by
                        simpa [length] using (congrArg Prod.fst run).symm
                      have nextEq : next =
                          setVars returns results
                            { { last with clock := min callState.clock last.clock } with
                              locals := env
                              stack := state.stack
                              localsSize := state.localsSize } := by
                        simpa [length] using (congrArg Prod.snd run).symm
                      subst resEq
                      subst nextEq
                      refine ⟨?_, ?_, ?_⟩
                      · simp only [setVars]
                      · simp only [setVars, lastHandler, callHandler]
                      · intro xs lsz len
                        obtain ⟨lss, sfs, smx, phl, bodyTarget⟩ :=
                          bodyHall (Stack.env lsz env :: xs) size (by
                            rw [callStack]
                            simp only [List.length_cons, len])
                        let targetCall := DataSem.callEnv args size
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
                        refine ⟨lsz, safe', mx', peak', ?_⟩
                        rw [← targetEq, bridge, moved]
                        have clockEq : min callState.clock last.clock =
                            min targetCall.clock movedState.clock := rfl
                        simp only [length, clockEq, if_true]
                        rfl
                  · simp only [length, typeError] at run
                    obtain ⟨rfl, rfl⟩ := run
                    trivial
                | err error =>
                  cases error with
                  | abort a =>
                    cases a with
                    | typeError =>
                      simp only [Prod.mk.injEq] at run
                      obtain ⟨rfl, rfl⟩ := run
                      trivial
                    | timeoutError =>
                      simp only [Prod.mk.injEq] at run
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
                          rw [callStack]
                          simp only [List.length_cons, len])
                      let targetCall := DataSem.callEnv args size
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
                      simp only [Prod.mk.injEq] at run
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
                          rw [callStack]
                          simp only [List.length_cons, len])
                      let targetCall := DataSem.callEnv args size
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
                    simp only [Prod.mk.injEq] at run
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
                    let targetCall := DataSem.callEnv args size
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
      · simp only [evaluate, vars, found, distinct, typeError] at run
        obtain ⟨rfl, rfl⟩ := run
        trivial

/-- The state at which a raising returning call evaluates its handler body,
    written in the shape that the stack-and-locals-swapped call state has.
    Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem handlerSwapState {C F : Type} (state last : State C F)
    (env : Spt DataSem.Value) (xs : List Stack) (lss : Option Nat) (smx : Option Nat)
    (sfs : Bool) (phl : Nat) (handlerName : Nat) (value : DataSem.Value)
    (callState targetCall : State C F)
    (clampedLocals :
      ({ last with clock := min callState.clock last.clock } : State C F).locals = env)
    (clampedHandler :
      ({ last with clock := min callState.clock last.clock } : State C F).handler =
        state.handler)
    (clockEq : min callState.clock last.clock = min targetCall.clock last.clock) :
    setVar handlerName value
        { last with
          stack := xs
          handler := state.handler
          locals := env
          localsSize := lss
          safeForSpace := sfs
          stackMax := smx
          peakHeapLength := phl
          clock := min targetCall.clock last.clock } =
      { { setVar handlerName value
            { last with clock := min callState.clock last.clock } with
          stack := xs
          localsSize := lss } with
        stackMax := smx
        safeForSpace := sfs
        peakHeapLength := phl } := by
  simp only [setVar, ← clampedLocals, ← clampedHandler, clockEq]

/-- The `Call` case of the stack-and-locals swap induction for a returning call
    whose callee raises into an installed handler: the handler body runs from the
    raised value at the unwound state. Flapjack infrastructure toward the port of
    HOL `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem stackLocalsSwap_returningCall_handler {C F : Type} (dest : Option Nat)
    (names : List Nat) (returns : List Nat) (live : NumSet) (state : State C F)
    (handlerName : Nat) (handlerBody : DataLang.Prog)
    (bodyIH : ∀ (body : DataLang.Prog) (called : State C F),
      called.clock < state.clock → StackLocalsSwapAt body called) :
    StackLocalsSwapAt (.call (some (returns, live)) dest names
      (some (handlerName, handlerBody))) state := by
  intro res next run
  cases vars : DataSem.getVars names state.locals with
  | none =>
    simp only [evaluate, vars, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    trivial
  | some values =>
    cases found : findCode dest values state.code state.stackFrameSizes with
    | none =>
      simp only [evaluate, vars, found, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      trivial
    | some entry =>
      obtain ⟨args, body, size⟩ := entry
      by_cases distinct : returns.Nodup
      · cases cut : cutEnv live state.locals with
        | none =>
          simp only [evaluate, vars, found, distinct, cut, typeError] at run
          obtain ⟨rfl, rfl⟩ := run
          trivial
        | some env =>
          by_cases zero : state.clock = 0
          · simp only [evaluate, vars, found, distinct, cut, zero, timeoutError] at run
            obtain ⟨rfl, rfl⟩ := run
            refine ⟨?_, ?_⟩
            · simp
            · intro xs lsz len
              let targetCall := DataSem.callEnv args size
                (DataSem.pushEnv env true
                  (DataSem.decClock { state with stack := xs, localsSize := lsz }))
              refine ⟨size, targetCall.safeForSpace, targetCall.stackMax,
                targetCall.peakHeapLength, ?_⟩
              simp only [evaluate, vars, found, distinct, cut, zero, timeoutError]
              simp only [targetCall, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock,
                Option.isSome_some, if_true, Bool.false_eq_true, if_false, decide_true,
                Bool.not_true]
              rw [← zero, len]
          · let callState := DataSem.callEnv args size
              (DataSem.pushEnv env true (DataSem.decClock state))
            have clockLt : callState.clock < state.clock := by
              simp only [callState, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock]
              omega
            have callStack : callState.stack =
                Stack.exc state.localsSize env state.handler :: state.stack := rfl
            have callHandler : callState.handler = state.stack.length := rfl
            cases bodyRun : evaluate body callState with
            | mk outcome last =>
              simp only [evaluate, vars, found, distinct, cut, zero, if_false,
                Option.isSome_some, Bool.false_eq_true, decide_true, Bool.not_true] at run ⊢
              simp only [callState] at bodyRun
              rw [bodyRun] at run
              simp only [fixClock] at run ⊢
              cases outcome with
              | none =>
                simp only [typeError, Prod.mk.injEq] at run
                obtain ⟨rfl, rfl⟩ := run
                trivial
              | some outcome =>
                cases outcome with
                | val results =>
                  by_cases length : results.length = returns.length
                  · revert run
                    cases popped : popEnv
                        { last with clock := min callState.clock last.clock } with
                    | none =>
                      intro run
                      simp only [length, typeError] at run
                      obtain ⟨rfl, rfl⟩ := run
                      trivial
                    | some final =>
                      intro run
                      have bodyArm :=
                        bodyIH body callState clockLt (some (.val results)) last bodyRun
                      obtain ⟨lastStack, lastHandler, bodyHall⟩ := bodyArm
                      have poppedEq := popEnv_pushedFrame (some (handlerName, handlerBody))
                        state { last with clock := min callState.clock last.clock }
                        env state.localsSize state.stack lastStack
                      have finalEq : final =
                          { { last with clock := min callState.clock last.clock } with
                            locals := env
                            stack := state.stack
                            localsSize := state.localsSize
                            handler := state.handler } := by
                        rw [poppedEq] at popped
                        injection popped with h
                        exact h.symm
                      rw [finalEq] at run
                      have resEq : res = none := by
                        simpa [length] using (congrArg Prod.fst run).symm
                      have nextEq : next =
                          setVars returns results
                            { { last with clock := min callState.clock last.clock } with
                              locals := env
                              stack := state.stack
                              localsSize := state.localsSize
                              handler := state.handler } := by
                        simpa [length] using (congrArg Prod.snd run).symm
                      subst resEq
                      subst nextEq
                      refine ⟨?_, ?_, ?_⟩
                      · simp only [setVars]
                      · simp only [setVars]
                      · intro xs lsz len
                        obtain ⟨lss, sfs, smx, phl, bodyTarget⟩ :=
                          bodyHall (Stack.exc lsz env state.handler :: xs) size (by
                            rw [callStack]
                            simp only [List.length_cons, len])
                        let targetCall := DataSem.callEnv args size
                          (DataSem.pushEnv env true
                            (DataSem.decClock { state with stack := xs, localsSize := lsz }))
                        have targetEq : targetCall =
                            DataSem.callEnv args size
                              (DataSem.pushEnv env true
                                (DataSem.decClock { state with
                                  stack := xs
                                  localsSize := lsz })) := rfl
                        obtain ⟨mx', safe', peak', moved⟩ :=
                          evaluate_stackSafePeakSwap targetCall.stackMax targetCall.safeForSpace
                            _ _ _ targetCall.peakHeapLength body bodyTarget
                        have bridge : targetCall =
                            { { callState with
                                stack := Stack.exc lsz env state.handler :: xs
                                localsSize := size } with
                              stackMax := targetCall.stackMax
                              safeForSpace := targetCall.safeForSpace
                              peakHeapLength := targetCall.peakHeapLength } := by
                          simp only [targetCall, callState, DataSem.callEnv, DataSem.pushEnv,
                            DataSem.decClock, if_true, len]
                        let movedState : State C F :=
                          { { last with
                              localsSize := lss
                              stack := Stack.exc lsz env state.handler :: xs
                              safeForSpace := sfs
                              stackMax := smx
                              peakHeapLength := phl } with
                            stackMax := mx'
                            safeForSpace := safe'
                            peakHeapLength := peak' }
                        refine ⟨lsz, safe', mx', peak', ?_⟩
                        rw [← targetEq, bridge, moved]
                        have clockEq : min callState.clock last.clock =
                            min targetCall.clock movedState.clock := rfl
                        simp only [length, clockEq, if_true]
                        rfl
                  · simp only [length, typeError] at run
                    obtain ⟨rfl, rfl⟩ := run
                    trivial
                | err error =>
                  cases error with
                  | abort a =>
                    cases a with
                    | typeError =>
                      simp only [Prod.mk.injEq] at run
                      obtain ⟨rfl, rfl⟩ := run
                      trivial
                    | timeoutError =>
                      simp only [Prod.mk.injEq] at run
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
                        bodyHall (Stack.exc lsz env state.handler :: xs) size (by
                          rw [callStack]
                          simp only [List.length_cons, len])
                      let targetCall := DataSem.callEnv args size
                        (DataSem.pushEnv env true
                          (DataSem.decClock { state with stack := xs, localsSize := lsz }))
                      have targetEq : targetCall =
                          DataSem.callEnv args size
                            (DataSem.pushEnv env true
                              (DataSem.decClock { state with
                                stack := xs
                                localsSize := lsz })) := rfl
                      obtain ⟨mx', safe', peak', moved⟩ :=
                        evaluate_stackSafePeakSwap targetCall.stackMax targetCall.safeForSpace
                          _ _ _ targetCall.peakHeapLength body bodyTarget
                      have bridge : targetCall =
                          { { callState with
                              stack := Stack.exc lsz env state.handler :: xs
                              localsSize := size } with
                            stackMax := targetCall.stackMax
                            safeForSpace := targetCall.safeForSpace
                            peakHeapLength := targetCall.peakHeapLength } := by
                        simp only [targetCall, callState, DataSem.callEnv, DataSem.pushEnv,
                          DataSem.decClock, if_true, len]
                      refine ⟨lss, safe', mx', peak', ?_⟩
                      rw [← targetEq, bridge, moved]
                    | ffiError event =>
                      simp only [Prod.mk.injEq] at run
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
                        bodyHall (Stack.exc lsz env state.handler :: xs) size (by
                          rw [callStack]
                          simp only [List.length_cons, len])
                      let targetCall := DataSem.callEnv args size
                        (DataSem.pushEnv env true
                          (DataSem.decClock { state with stack := xs, localsSize := lsz }))
                      have targetEq : targetCall =
                          DataSem.callEnv args size
                            (DataSem.pushEnv env true
                              (DataSem.decClock { state with
                                stack := xs
                                localsSize := lsz })) := rfl
                      obtain ⟨mx', safe', peak', moved⟩ :=
                        evaluate_stackSafePeakSwap targetCall.stackMax targetCall.safeForSpace
                          _ _ _ targetCall.peakHeapLength body bodyTarget
                      have bridge : targetCall =
                          { { callState with
                              stack := Stack.exc lsz env state.handler :: xs
                              localsSize := size } with
                            stackMax := targetCall.stackMax
                            safeForSpace := targetCall.safeForSpace
                            peakHeapLength := targetCall.peakHeapLength } := by
                        simp only [targetCall, callState, DataSem.callEnv, DataSem.pushEnv,
                          DataSem.decClock, if_true, len]
                      refine ⟨lss, safe', mx', peak', ?_⟩
                      rw [← targetEq, bridge, moved]
                  | raise t =>
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
                    have s2Eq : s2 =
                        { callState with
                          handler := state.handler
                          locals := env
                          stack := state.stack
                          localsSize := state.localsSize } := by
                      have computed := jumpExc_excHead callState state.localsSize env
                        state.handler state.stack callStack callHandler
                      rw [computed] at jumped
                      injection jumped with h
                      exact h.symm
                    let clampedLast : State C F :=
                      { last with clock := min callState.clock last.clock }
                    have clampedLocals : clampedLast.locals = env := by
                      simp only [clampedLast, ← localsEq, s2Eq]
                    have clampedStack : clampedLast.stack = state.stack := by
                      simp only [clampedLast, ← stackEq, s2Eq]
                    have clampedHandler : clampedLast.handler = state.handler := by
                      simp only [clampedLast, ← handlerEq, s2Eq]
                    let handlerState : State C F := setVar handlerName t clampedLast
                    have handlerStackEq : handlerState.stack = state.stack := by
                      simp only [handlerState, setVar, clampedStack]
                    have handlerHandlerEq : handlerState.handler = state.handler := by
                      simp only [handlerState, setVar, clampedHandler]
                    have handlerClockLt : handlerState.clock < state.clock := by
                      have bound : min callState.clock last.clock ≤ callState.clock :=
                        min_le_left _ _
                      simp only [handlerState, setVar, clampedLast]
                      exact Nat.lt_of_le_of_lt bound clockLt
                    have runForward : evaluate handlerBody handlerState = (res, next) := by
                      rw [← run]
                    clear run
                    cases handlerRun : evaluate handlerBody handlerState with
                    | mk houtcome hlast =>
                      have pairEq : (res, next) = (houtcome, hlast) := by
                        rw [← runForward, handlerRun]
                      simp only [Prod.mk.injEq] at pairEq
                      obtain ⟨resEq, nextEq⟩ := pairEq
                      rw [resEq, nextEq]
                      have handlerIH := bodyIH handlerBody handlerState handlerClockLt
                      cases houtcome with
                      | none =>
                        obtain ⟨handlerStack, handlerHandler, handlerHall⟩ :=
                          handlerIH none hlast handlerRun
                        refine ⟨?_, ?_, ?_⟩
                        · simp only [handlerStack, handlerState, setVar, clampedStack]
                        · simp only [handlerHandler, handlerState, setVar, clampedHandler]
                        · intro xs lsz len
                          let targetCall := DataSem.callEnv args size
                            (DataSem.pushEnv env true
                              (DataSem.decClock { state with stack := xs, localsSize := lsz }))
                          have targetStack : targetCall.stack =
                              Stack.exc lsz env state.handler :: xs := rfl
                          have targetHandler : targetCall.handler = xs.length := by
                            simp only [targetCall, DataSem.callEnv, DataSem.pushEnv,
                              DataSem.decClock, if_true]
                          have targetJumped : jumpExc targetCall = some
                              { targetCall with
                                handler := state.handler
                                locals := env
                                stack := xs
                                localsSize := lsz } :=
                            jumpExc_excHead targetCall lsz env state.handler xs
                              targetStack targetHandler
                          obtain ⟨lss, sfs, smx, phl, bodyTarget⟩ :=
                            callBody_raiseTarget args size env (some (handlerName, handlerBody))
                              body state callState last t xs lsz rfl len targetJumped rfl rfl rfl
                              bodyHall
                          simp only [Option.isSome_some] at bodyTarget
                          have handlerLen : handlerState.stack.length = xs.length := by
                            simp only [handlerStackEq, len]
                          obtain ⟨lss', sfs', smx', phl', handlerTarget⟩ :=
                            handlerHall xs lss handlerLen
                          obtain ⟨mx'', safe'', peak'', handlerMoved⟩ :=
                            evaluate_stackSafePeakSwap smx sfs _ _ _ phl handlerBody handlerTarget
                          rw [bodyTarget]
                          simp only []
                          have clockEq : min callState.clock last.clock =
                              min (DataSem.callEnv args size
                                (DataSem.pushEnv env true
                                  (DataSem.decClock { state with
                                    stack := xs
                                    localsSize := lsz }))).clock last.clock := rfl
                          rw [handlerSwapState state last env xs lss smx sfs phl handlerName t
                            callState
                            (DataSem.callEnv args size
                              (DataSem.pushEnv env true
                                (DataSem.decClock { state with
                                  stack := xs
                                  localsSize := lsz })))
                            clampedLocals clampedHandler clockEq]
                          rw [handlerMoved]
                          exact ⟨lss', safe'', mx'', peak'', rfl⟩
                      | some hresult =>
                        cases hresult with
                        | val _ =>
                          obtain ⟨handlerStack, handlerHandler, handlerHall⟩ :=
                            handlerIH (some (.val _)) hlast handlerRun
                          refine ⟨?_, ?_, ?_⟩
                          · simp only [handlerStack, handlerState, setVar, clampedStack]
                          · simp only [handlerHandler, handlerState, setVar, clampedHandler]
                          · intro xs lsz len
                            let targetCall := DataSem.callEnv args size
                              (DataSem.pushEnv env true
                                (DataSem.decClock { state with stack := xs, localsSize := lsz }))
                            have targetStack : targetCall.stack =
                                Stack.exc lsz env state.handler :: xs := rfl
                            have targetHandler : targetCall.handler = xs.length := by
                              simp only [targetCall, DataSem.callEnv, DataSem.pushEnv,
                                DataSem.decClock, if_true]
                            have targetJumped : jumpExc targetCall = some
                                { targetCall with
                                  handler := state.handler
                                  locals := env
                                  stack := xs
                                  localsSize := lsz } :=
                              jumpExc_excHead targetCall lsz env state.handler xs
                                targetStack targetHandler
                            obtain ⟨lss, sfs, smx, phl, bodyTarget⟩ :=
                              callBody_raiseTarget args size env (some (handlerName, handlerBody))
                                body state callState last t xs lsz rfl len targetJumped rfl rfl rfl
                                bodyHall
                            simp only [Option.isSome_some] at bodyTarget
                            have handlerLen : handlerState.stack.length = xs.length := by
                              simp only [handlerStackEq, len]
                            obtain ⟨lss', sfs', smx', phl', handlerTarget⟩ :=
                              handlerHall xs lss handlerLen
                            obtain ⟨mx'', safe'', peak'', handlerMoved⟩ :=
                              evaluate_stackSafePeakSwap smx sfs _ _ _ phl handlerBody
                                handlerTarget
                            rw [bodyTarget]
                            simp only []
                            have clockEq : min callState.clock last.clock =
                                min (DataSem.callEnv args size
                                  (DataSem.pushEnv env true
                                    (DataSem.decClock { state with
                                      stack := xs
                                      localsSize := lsz }))).clock last.clock := rfl
                            rw [handlerSwapState state last env xs lss smx sfs phl handlerName t
                              callState
                              (DataSem.callEnv args size
                                (DataSem.pushEnv env true
                                  (DataSem.decClock { state with
                                    stack := xs
                                    localsSize := lsz })))
                              clampedLocals clampedHandler clockEq]
                            rw [handlerMoved]
                            exact ⟨lss', safe'', mx'', peak'', rfl⟩
                        | err herror =>
                          cases herror with
                          | abort a =>
                            cases a with
                            | typeError =>
                              exact trivial
                            | timeoutError =>
                              obtain ⟨handlerEmpty, handlerHall⟩ :=
                                handlerIH (some (.err (.abort .timeoutError))) hlast handlerRun
                              refine ⟨handlerEmpty, ?_⟩
                              intro xs lsz len
                              let targetCall := DataSem.callEnv args size
                                (DataSem.pushEnv env true
                                  (DataSem.decClock { state with
                                    stack := xs
                                    localsSize := lsz }))
                              have targetStack : targetCall.stack =
                                  Stack.exc lsz env state.handler :: xs := rfl
                              have targetHandler : targetCall.handler = xs.length := by
                                simp only [targetCall, DataSem.callEnv, DataSem.pushEnv,
                                  DataSem.decClock, if_true]
                              have targetJumped : jumpExc targetCall = some
                                  { targetCall with
                                    handler := state.handler
                                    locals := env
                                    stack := xs
                                    localsSize := lsz } :=
                                jumpExc_excHead targetCall lsz env state.handler xs
                                  targetStack targetHandler
                              obtain ⟨lss, sfs, smx, phl, bodyTarget⟩ :=
                                callBody_raiseTarget args size env
                                  (some (handlerName, handlerBody))
                                  body state callState last t xs lsz rfl len targetJumped
                                  rfl rfl rfl bodyHall
                              simp only [Option.isSome_some] at bodyTarget
                              have handlerLen : handlerState.stack.length = xs.length := by
                                simp only [handlerStackEq, len]
                              obtain ⟨lss', sfs', smx', phl', handlerTarget⟩ :=
                                handlerHall xs lss handlerLen
                              obtain ⟨mx'', safe'', peak'', handlerMoved⟩ :=
                                evaluate_stackSafePeakSwap smx sfs _ _ _ phl handlerBody
                                  handlerTarget
                              rw [bodyTarget]
                              simp only []
                              have clockEq : min callState.clock last.clock =
                                  min (DataSem.callEnv args size
                                    (DataSem.pushEnv env true
                                      (DataSem.decClock { state with
                                        stack := xs
                                        localsSize := lsz }))).clock last.clock := rfl
                              rw [handlerSwapState state last env xs lss smx sfs phl
                                handlerName t
                                callState
                                (DataSem.callEnv args size
                                  (DataSem.pushEnv env true
                                    (DataSem.decClock { state with
                                      stack := xs
                                      localsSize := lsz })))
                                clampedLocals clampedHandler clockEq]
                              rw [handlerMoved]
                              exact ⟨lss', safe'', mx'', peak'', rfl⟩
                            | ffiError event =>
                              obtain ⟨handlerEmpty, handlerHall⟩ :=
                                handlerIH (some (.err (.abort (.ffiError event)))) hlast
                                  handlerRun
                              refine ⟨handlerEmpty, ?_⟩
                              intro xs lsz len
                              let targetCall := DataSem.callEnv args size
                                (DataSem.pushEnv env true
                                  (DataSem.decClock { state with
                                    stack := xs
                                    localsSize := lsz }))
                              have targetStack : targetCall.stack =
                                  Stack.exc lsz env state.handler :: xs := rfl
                              have targetHandler : targetCall.handler = xs.length := by
                                simp only [targetCall, DataSem.callEnv, DataSem.pushEnv,
                                  DataSem.decClock, if_true]
                              have targetJumped : jumpExc targetCall = some
                                  { targetCall with
                                    handler := state.handler
                                    locals := env
                                    stack := xs
                                    localsSize := lsz } :=
                                jumpExc_excHead targetCall lsz env state.handler xs
                                  targetStack targetHandler
                              obtain ⟨lss, sfs, smx, phl, bodyTarget⟩ :=
                                callBody_raiseTarget args size env
                                  (some (handlerName, handlerBody))
                                  body state callState last t xs lsz rfl len targetJumped
                                  rfl rfl rfl bodyHall
                              simp only [Option.isSome_some] at bodyTarget
                              have handlerLen : handlerState.stack.length = xs.length := by
                                simp only [handlerStackEq, len]
                              obtain ⟨lss', sfs', smx', phl', handlerTarget⟩ :=
                                handlerHall xs lss handlerLen
                              obtain ⟨mx'', safe'', peak'', handlerMoved⟩ :=
                                evaluate_stackSafePeakSwap smx sfs _ _ _ phl handlerBody
                                  handlerTarget
                              rw [bodyTarget]
                              simp only []
                              have clockEq : min callState.clock last.clock =
                                  min (DataSem.callEnv args size
                                    (DataSem.pushEnv env true
                                      (DataSem.decClock { state with
                                        stack := xs
                                        localsSize := lsz }))).clock last.clock := rfl
                              rw [handlerSwapState state last env xs lss smx sfs phl
                                handlerName t
                                callState
                                (DataSem.callEnv args size
                                  (DataSem.pushEnv env true
                                    (DataSem.decClock { state with
                                      stack := xs
                                      localsSize := lsz })))
                                clampedLocals clampedHandler clockEq]
                              rw [handlerMoved]
                              exact ⟨lss', safe'', mx'', peak'', rfl⟩
                          | raise t' =>
                            obtain ⟨h2, handlerJumpedState, handlerLocals, handlerStack,
                              handlerHandler, handlerHall⟩ :=
                              handlerIH (some (.err (.raise t'))) hlast handlerRun
                            have stateJumped : jumpExc state = some
                                { state with
                                  stack := h2.stack
                                  handler := h2.handler
                                  locals := h2.locals
                                  localsSize := h2.localsSize } :=
                              jumpExc_transport handlerState state h2
                                (by simp only [handlerStackEq])
                                (by simp only [handlerHandlerEq]) handlerJumpedState
                            refine ⟨_, stateJumped, ?_, ?_, ?_, ?_⟩
                            · simp only [handlerLocals]
                            · simp only [handlerStack]
                            · simp only [handlerHandler]
                            · intro xs s7 lsz jumpedRun len
                              let targetCall := DataSem.callEnv args size
                                (DataSem.pushEnv env true
                                  (DataSem.decClock { state with
                                    stack := xs
                                    localsSize := lsz }))
                              have targetStack : targetCall.stack =
                                  Stack.exc lsz env state.handler :: xs := rfl
                              have targetHandler : targetCall.handler = xs.length := by
                                simp only [targetCall, DataSem.callEnv, DataSem.pushEnv,
                                  DataSem.decClock, if_true]
                              have targetJumped : jumpExc targetCall = some
                                  { targetCall with
                                    handler := state.handler
                                    locals := env
                                    stack := xs
                                    localsSize := lsz } :=
                                jumpExc_excHead targetCall lsz env state.handler xs
                                  targetStack targetHandler
                              obtain ⟨lss, sfs, smx, phl, bodyTarget⟩ :=
                                callBody_raiseTarget args size env
                                  (some (handlerName, handlerBody))
                                  body state callState last t xs lsz rfl len targetJumped
                                  rfl rfl rfl bodyHall
                              have handlerLen : handlerState.stack.length = xs.length := by
                                simp only [handlerStackEq, len]
                              have handlerJumped : jumpExc
                                  { handlerState with stack := xs, localsSize := lss } = some
                                  { { handlerState with stack := xs, localsSize := lss } with
                                    stack := s7.stack
                                    handler := s7.handler
                                    locals := s7.locals
                                    localsSize := s7.localsSize } :=
                                jumpExc_transport { state with stack := xs, localsSize := lsz }
                                  { handlerState with stack := xs, localsSize := lss } s7 rfl
                                  (by simp only [handlerHandlerEq]) jumpedRun
                              obtain ⟨lss', sfs', smx', phl', handlerTarget⟩ :=
                                handlerHall xs _ lss handlerJumped handlerLen
                              obtain ⟨mx'', safe'', peak'', handlerMoved⟩ :=
                                evaluate_stackSafePeakSwap smx sfs _ _ _ phl handlerBody
                                  handlerTarget
                              simp only [Option.isSome_some] at bodyTarget
                              rw [bodyTarget]
                              simp only []
                              have clockEq : min callState.clock last.clock =
                                  min (DataSem.callEnv args size
                                    (DataSem.pushEnv env true
                                      (DataSem.decClock { state with
                                        stack := xs
                                        localsSize := lsz }))).clock last.clock := rfl
                              rw [handlerSwapState state last env xs lss smx sfs phl
                                handlerName t
                                callState
                                (DataSem.callEnv args size
                                  (DataSem.pushEnv env true
                                    (DataSem.decClock { state with
                                      stack := xs
                                      localsSize := lsz })))
                                clampedLocals clampedHandler clockEq]
                              rw [handlerMoved]
                              exact ⟨lss', safe'', mx'', peak'', rfl⟩
      · simp only [evaluate, vars, found, distinct, typeError] at run
        obtain ⟨rfl, rfl⟩ := run
        trivial

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

/-- Installation commutes with replacing the stack and the locals size: it
    reads only the compiler state, and reports the same value with the frame
    fields replaced. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem doInstall_swapStackLocals_map {C F : Type} (args : List DataSem.Value)
    (state : State C F) (xs : List Stack) (lsz : Option Nat) :
    doInstall (C := C) (F := F) (R := DataSem.Value) args
        { state with stack := xs, localsSize := lsz } =
      Flapjack.SemanticPrimitivesProps.mapResult
        (fun (pair : DataSem.Value × State C F) =>
          (pair.1, { pair.2 with stack := xs, localsSize := lsz }))
        id (doInstall (C := C) (F := F) (R := DataSem.Value) args state) := by
  simp only [doInstall, Flapjack.SemanticPrimitivesProps.mapResult,
    Flapjack.SemanticPrimitivesProps.mapErrorResult]
  repeat' (split <;> try rfl)

/-- Successful installation at a stack-and-locals-swapped state. Flapjack
    infrastructure toward the port of HOL `evaluate_stack_and_locals_swap`;
    no separate HOL original. -/
private theorem doInstall_swapStackLocals_val {C F : Type} (args : List DataSem.Value)
    (state : State C F) (xs : List Stack) (lsz : Option Nat) (value : DataSem.Value)
    (next : State C F)
    (run : doInstall (C := C) (F := F) (R := DataSem.Value) args state = .val (value, next)) :
    doInstall (C := C) (F := F) (R := DataSem.Value) args
        { state with stack := xs, localsSize := lsz } =
      .val (value, { next with stack := xs, localsSize := lsz }) := by
  have mapped := doInstall_swapStackLocals_map args state xs lsz
  rw [mapped, run]
  simp only [Flapjack.SemanticPrimitivesProps.mapResult]

/-- Failing installation fails identically at a stack-and-locals-swapped state.
    Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem doInstall_swapStackLocals_err {C F : Type} (args : List DataSem.Value)
    (state : State C F) (xs : List Stack) (lsz : Option Nat)
    (error : ErrorResult DataSem.Value)
    (run : doInstall (C := C) (F := F) (R := DataSem.Value) args state = .err error) :
    doInstall (C := C) (F := F) (R := DataSem.Value) args
        { state with stack := xs, localsSize := lsz } = .err error := by
  have mapped := doInstall_swapStackLocals_map args state xs lsz
  rw [mapped, run]
  simp only [Flapjack.SemanticPrimitivesProps.mapResult]
  rw [Flapjack.SemanticPrimitivesProps.mapErrorResult_id]

/-- Auxiliary application commutes with replacing the stack and the locals
    size: it reads neither, so it reports the same value with the frame fields
    replaced. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem doAppAux_swapStackLocals_map {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (xs : List Stack) (lsz : Option Nat) :
    doAppAux op values { state with stack := xs, localsSize := lsz } =
      Flapjack.SemanticPrimitivesProps.mapResult
        (fun (pair : DataSem.Value × State C F) =>
          (pair.1, { pair.2 with stack := xs, localsSize := lsz }))
        id (doAppAux op values state) := by
  have changed := doAppAux_withFields op values state xs lsz state.stackMax
    state.peakHeapLength state.locals state.space state.handler state.clock
    state.stackFrameSizes state.compile
  cases run : doAppAux op values state with
  | err error =>
    simpa [run, Flapjack.SemanticPrimitivesProps.mapResult,
      Flapjack.SemanticPrimitivesProps.mapErrorResult] using changed
  | val pair =>
    obtain ⟨value, next⟩ := pair
    have frame := doAppAux_fieldFrame op values state next value run
    simpa [run, Flapjack.SemanticPrimitivesProps.mapResult, frame.1, frame.2.1,
      frame.2.2.1, frame.2.2.2.1, frame.2.2.2.2.1, frame.2.2.2.2.2.1, frame.2.2.2.2.2.2.1,
      frame.2.2.2.2.2.2.2.1, frame.2.2.2.2.2.2.2.2.1, frame.2.2.2.2.2.2.2.2.2] using changed

/-- Successful auxiliary application at a stack-and-locals-swapped state.
    Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem doAppAux_swapStackLocals_val {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (xs : List Stack) (lsz : Option Nat)
    (value : DataSem.Value) (next : State C F)
    (run : doAppAux op values state = .val (value, next)) :
    doAppAux op values { state with stack := xs, localsSize := lsz } =
      .val (value, { next with stack := xs, localsSize := lsz }) := by
  have mapped := doAppAux_swapStackLocals_map op values state xs lsz
  rw [mapped, run]
  simp only [Flapjack.SemanticPrimitivesProps.mapResult]

/-- Failing auxiliary application fails identically at a stack-and-locals-swapped
    state. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem doAppAux_swapStackLocals_err {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (xs : List Stack) (lsz : Option Nat)
    (error : ErrorResult DataSem.Value)
    (run : doAppAux op values state = .err error) :
    doAppAux op values { state with stack := xs, localsSize := lsz } = .err error := by
  have mapped := doAppAux_swapStackLocals_map op values state xs lsz
  rw [mapped, run]
  simp only [Flapjack.SemanticPrimitivesProps.mapResult]
  rw [Flapjack.SemanticPrimitivesProps.mapErrorResult_id]

/-- Successful auxiliary application at a state whose stack, locals size,
    safety flag, stack maximum and peak-heap estimate are replaced: it reads
    none of those fields, so only the safety flag is left free. Flapjack
    infrastructure toward the port of HOL `evaluate_stack_and_locals_swap`;
    no separate HOL original. -/
private theorem doAppAux_swapStackLocalsFields_val {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (xs : List Stack) (lsz : Option Nat)
    (safe : Bool) (smx : Option Nat) (phl : Nat) (value : DataSem.Value) (next : State C F)
    (run : doAppAux op values state = .val (value, next)) :
    ∃ sfs, doAppAux op values
        { state with
          stack := xs
          localsSize := lsz
          safeForSpace := safe
          stackMax := smx
          peakHeapLength := phl } =
      .val (value, { next with
        stack := xs
        localsSize := lsz
        safeForSpace := sfs
        stackMax := smx
        peakHeapLength := phl }) := by
  obtain ⟨safe', first⟩ :=
    doAppAux_safePeakStackMax op values state next value safe smx phl run
  have fields := doAppAux_withFields op values
    { state with safeForSpace := safe, stackMax := smx, peakHeapLength := phl }
    xs lsz smx phl state.locals state.space state.handler state.clock state.stackFrameSizes
    state.compile
  rw [first] at fields
  have frame := doAppAux_fieldFrame op values state next value run
  refine ⟨safe', ?_⟩
  simpa [Flapjack.SemanticPrimitivesProps.mapResult, frame.1, frame.2.1,
    frame.2.2.1, frame.2.2.2.1, frame.2.2.2.2.1, frame.2.2.2.2.2.1, frame.2.2.2.2.2.2.1,
    frame.2.2.2.2.2.2.2.1, frame.2.2.2.2.2.2.2.2.1, frame.2.2.2.2.2.2.2.2.2] using fields

/-- The limit and stack stages at a stack-and-locals-swapped state report the
    source's stack accounting with the frame fields replaced and the resource
    observations free. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem doStack_doLimSafe_swapStackLocals {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (xs : List Stack) (lsz : Option Nat)
    (safe : Bool) (peak : Nat) :
    ∃ sfs smx phl,
      doStack op values (doLimSafe { state with
          stack := xs
          localsSize := lsz
          safeForSpace := safe
          peakHeapLength := peak } op values) =
        { doStack op values (doLimSafe state op values) with
          stack := xs
          localsSize := lsz
          safeForSpace := sfs
          stackMax := smx
          peakHeapLength := phl } := by
  let result := doStack op values (doLimSafe { state with
    stack := xs
    localsSize := lsz
    safeForSpace := safe
    peakHeapLength := peak } op values)
  refine ⟨result.safeForSpace, result.stackMax, result.peakHeapLength, ?_⟩
  rfl

/-- The space, limit, stack and auxiliary stages carry a successful result
    across a stack-and-locals replacement. Flapjack infrastructure toward the
    port of HOL `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem doAppGeneric_swapStackLocals_val {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (xs : List Stack) (lsz : Option Nat)
    (value : DataSem.Value) (next : State C F)
    (run : (match doSpace op values state with
      | none => (Result.err (.abort .typeError) :
          Result (DataSem.Value × State C F) DataSem.Value)
      | some mid => doAppAux op values (doStack op values (doLimSafe mid op values))) =
        .val (value, next)) :
    ∃ sfs smx phl,
      (match doSpace op values { state with stack := xs, localsSize := lsz } with
      | none => (Result.err (.abort .typeError) :
          Result (DataSem.Value × State C F) DataSem.Value)
      | some mid => doAppAux op values (doStack op values (doLimSafe mid op values))) =
        .val (value, { next with
          stack := xs
          localsSize := lsz
          safeForSpace := sfs
          stackMax := smx
          peakHeapLength := phl }) := by
  cases space : doSpace op values state with
  | none =>
    rw [space] at run
    cases run
  | some mid =>
    rw [space] at run
    obtain ⟨sfs1, phl1, spaceTarget⟩ :=
      doSpace_swapStackLocals op values state xs lsz mid space
    simp only [spaceTarget]
    obtain ⟨sfs2, smx2, phl2, stackTarget⟩ :=
      doStack_doLimSafe_swapStackLocals op values mid xs lsz sfs1 phl1
    simp only [stackTarget]
    obtain ⟨sfs3, aux⟩ :=
      doAppAux_swapStackLocalsFields_val op values
        (doStack op values (doLimSafe mid op values)) xs lsz sfs2 smx2 phl2 value next run
    exact ⟨sfs3, smx2, phl2, aux⟩

/-- The space, limit, stack and auxiliary stages carry a failing result across
    a stack-and-locals replacement. Flapjack infrastructure toward the port of
    HOL `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem doAppGeneric_swapStackLocals_err {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (xs : List Stack) (lsz : Option Nat)
    (error : ErrorResult DataSem.Value)
    (run : (match doSpace op values state with
      | none => (Result.err (.abort .typeError) :
          Result (DataSem.Value × State C F) DataSem.Value)
      | some mid => doAppAux op values (doStack op values (doLimSafe mid op values))) =
        .err error) :
    (match doSpace op values { state with stack := xs, localsSize := lsz } with
    | none => (Result.err (.abort .typeError) :
        Result (DataSem.Value × State C F) DataSem.Value)
    | some mid => doAppAux op values (doStack op values (doLimSafe mid op values))) =
      .err error := by
  cases space : doSpace op values state with
  | none =>
    have runNone : (Result.err (.abort .typeError) :
        Result (DataSem.Value × State C F) DataSem.Value) = .err error := by
      simpa [space] using run
    simp only [doSpace_swapStackLocals_none op values state xs lsz space]
    exact runNone
  | some mid =>
    rw [space] at run
    obtain ⟨sfs1, phl1, spaceTarget⟩ :=
      doSpace_swapStackLocals op values state xs lsz mid space
    simp only [spaceTarget]
    obtain ⟨sfs2, smx2, phl2, stackTarget⟩ :=
      doStack_doLimSafe_swapStackLocals op values mid xs lsz sfs1 phl1
    simp only [stackTarget]
    exact doAppAux_error_resource op values (doStack op values (doLimSafe mid op values))
      sfs2 phl2 smx2 xs lsz (doStack op values (doLimSafe mid op values)).locals
      (doStack op values (doLimSafe mid op values)).space error run

/-- A successful primitive application carries its value across a
    stack-and-locals replacement, with only the resource observations free.
    Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem doApp_swapStackLocals_val {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (xs : List Stack) (lsz : Option Nat)
    (value : DataSem.Value) (next : State C F)
    (run : doApp op values state = .val (value, next)) :
    ∃ sfs smx phl, doApp op values { state with stack := xs, localsSize := lsz } =
      .val (value, { next with
        stack := xs
        localsSize := lsz
        safeForSpace := sfs
        stackMax := smx
        peakHeapLength := phl }) := by
  cases op with
  | install =>
    simp only [doApp] at run ⊢
    have installed :=
      doInstall_swapStackLocals_val values
        { state with stackMax := none, stackFrameSizes := .ln } xs lsz value next run
    exact ⟨next.safeForSpace, next.stackMax, next.peakHeapLength, installed⟩
  | intOp inner =>
    cases inner with
    | greater =>
      simp only [doApp] at run
      cases run
    | greaterEq =>
      simp only [doApp] at run
      cases run
    | const i =>
      simp only [doApp] at run ⊢
      exact doAppGeneric_swapStackLocals_val (.intOp (.const i)) values state xs lsz value next run
    | add =>
      simp only [doApp] at run ⊢
      exact doAppGeneric_swapStackLocals_val (.intOp .add) values state xs lsz value next run
    | sub =>
      simp only [doApp] at run ⊢
      exact doAppGeneric_swapStackLocals_val (.intOp .sub) values state xs lsz value next run
    | mult =>
      simp only [doApp] at run ⊢
      exact doAppGeneric_swapStackLocals_val (.intOp .mult) values state xs lsz value next run
    | div =>
      simp only [doApp] at run ⊢
      exact doAppGeneric_swapStackLocals_val (.intOp .div) values state xs lsz value next run
    | mod =>
      simp only [doApp] at run ⊢
      exact doAppGeneric_swapStackLocals_val (.intOp .mod) values state xs lsz value next run
    | less =>
      simp only [doApp] at run ⊢
      exact doAppGeneric_swapStackLocals_val (.intOp .less) values state xs lsz value next run
    | lessEq =>
      simp only [doApp] at run ⊢
      exact doAppGeneric_swapStackLocals_val (.intOp .lessEq) values state xs lsz value next run
    | lessConstSmall n =>
      simp only [doApp] at run ⊢
      exact doAppGeneric_swapStackLocals_val (.intOp (.lessConstSmall n)) values state xs lsz
        value next run
  | label label =>
    simp only [doApp] at run ⊢
    exact doAppGeneric_swapStackLocals_val (.label label) values state xs lsz value next run
  | ffi name =>
    simp only [doApp] at run ⊢
    exact doAppGeneric_swapStackLocals_val (.ffi name) values state xs lsz value next run
  | wordOp inner =>
    simp only [doApp] at run ⊢
    exact doAppGeneric_swapStackLocals_val (.wordOp inner) values state xs lsz value next run
  | blockOp inner =>
    simp only [doApp] at run ⊢
    exact doAppGeneric_swapStackLocals_val (.blockOp inner) values state xs lsz value next run
  | globOp inner =>
    simp only [doApp] at run ⊢
    exact doAppGeneric_swapStackLocals_val (.globOp inner) values state xs lsz value next run
  | memOp inner =>
    simp only [doApp] at run ⊢
    exact doAppGeneric_swapStackLocals_val (.memOp inner) values state xs lsz value next run
  | thunkOp inner =>
    simp only [doApp] at run ⊢
    exact doAppGeneric_swapStackLocals_val (.thunkOp inner) values state xs lsz value next run

/-- A failing primitive application fails identically across a
    stack-and-locals replacement. Flapjack infrastructure toward the port of
    HOL `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem doApp_swapStackLocals_err {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (xs : List Stack) (lsz : Option Nat)
    (error : ErrorResult DataSem.Value)
    (run : doApp op values state = .err error) :
    doApp op values { state with stack := xs, localsSize := lsz } = .err error := by
  cases op with
  | install =>
    simp only [doApp] at run ⊢
    exact doInstall_swapStackLocals_err values
      { state with stackMax := none, stackFrameSizes := .ln } xs lsz error run
  | intOp inner =>
    cases inner with
    | greater =>
      simp only [doApp] at run ⊢
      exact run
    | greaterEq =>
      simp only [doApp] at run ⊢
      exact run
    | const i =>
      simp only [doApp] at run ⊢
      exact doAppGeneric_swapStackLocals_err (.intOp (.const i)) values state xs lsz error run
    | add =>
      simp only [doApp] at run ⊢
      exact doAppGeneric_swapStackLocals_err (.intOp .add) values state xs lsz error run
    | sub =>
      simp only [doApp] at run ⊢
      exact doAppGeneric_swapStackLocals_err (.intOp .sub) values state xs lsz error run
    | mult =>
      simp only [doApp] at run ⊢
      exact doAppGeneric_swapStackLocals_err (.intOp .mult) values state xs lsz error run
    | div =>
      simp only [doApp] at run ⊢
      exact doAppGeneric_swapStackLocals_err (.intOp .div) values state xs lsz error run
    | mod =>
      simp only [doApp] at run ⊢
      exact doAppGeneric_swapStackLocals_err (.intOp .mod) values state xs lsz error run
    | less =>
      simp only [doApp] at run ⊢
      exact doAppGeneric_swapStackLocals_err (.intOp .less) values state xs lsz error run
    | lessEq =>
      simp only [doApp] at run ⊢
      exact doAppGeneric_swapStackLocals_err (.intOp .lessEq) values state xs lsz error run
    | lessConstSmall n =>
      simp only [doApp] at run ⊢
      exact doAppGeneric_swapStackLocals_err (.intOp (.lessConstSmall n)) values state xs lsz
        error run
  | label label =>
    simp only [doApp] at run ⊢
    exact doAppGeneric_swapStackLocals_err (.label label) values state xs lsz error run
  | ffi name =>
    simp only [doApp] at run ⊢
    exact doAppGeneric_swapStackLocals_err (.ffi name) values state xs lsz error run
  | wordOp inner =>
    simp only [doApp] at run ⊢
    exact doAppGeneric_swapStackLocals_err (.wordOp inner) values state xs lsz error run
  | blockOp inner =>
    simp only [doApp] at run ⊢
    exact doAppGeneric_swapStackLocals_err (.blockOp inner) values state xs lsz error run
  | globOp inner =>
    simp only [doApp] at run ⊢
    exact doAppGeneric_swapStackLocals_err (.globOp inner) values state xs lsz error run
  | memOp inner =>
    simp only [doApp] at run ⊢
    exact doAppGeneric_swapStackLocals_err (.memOp inner) values state xs lsz error run
  | thunkOp inner =>
    simp only [doApp] at run ⊢
    exact doAppGeneric_swapStackLocals_err (.thunkOp inner) values state xs lsz error run

/-- The live-name cut commutes with replacing the stack and the locals size.
    Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem cutStateOpt_swapStackLocals {C F : Type} (live : Option NumSet)
    (state : State C F) (xs : List Stack) (lsz : Option Nat) :
    cutStateOpt live { state with stack := xs, localsSize := lsz } =
      (cutStateOpt live state).map
        (fun next => { next with stack := xs, localsSize := lsz }) := by
  cases live with
  | none => rfl
  | some names =>
    simp only [cutStateOpt, cutState]
    cases env : cutEnv names state.locals with
    | none => rfl
    | some value => rfl

/-- A successful live-name cut at a stack-and-locals-swapped state reports the
    source's cut state with the frame fields replaced. Flapjack infrastructure
    toward the port of HOL `evaluate_stack_and_locals_swap`; no separate HOL
    original. -/
private theorem cutStateOpt_swapStackLocals_val {C F : Type} (live : Option NumSet)
    (state : State C F) (xs : List Stack) (lsz : Option Nat) (next : State C F)
    (run : cutStateOpt live state = some next) :
    cutStateOpt live { state with stack := xs, localsSize := lsz } =
      some { next with stack := xs, localsSize := lsz } := by
  rw [cutStateOpt_swapStackLocals, run]
  rfl

/-- A failing live-name cut fails at a stack-and-locals-swapped state too.
    Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem cutStateOpt_swapStackLocals_none {C F : Type} (live : Option NumSet)
    (state : State C F) (xs : List Stack) (lsz : Option Nat)
    (run : cutStateOpt live state = none) :
    cutStateOpt live { state with stack := xs, localsSize := lsz } = none := by
  rw [cutStateOpt_swapStackLocals, run]
  rfl

/-- The live-name cut leaves the stack and the handler alone. Flapjack
    infrastructure toward the port of HOL `evaluate_stack_and_locals_swap`;
    no separate HOL original. -/
private theorem cutStateOpt_stack_handler {C F : Type} (live : Option NumSet)
    (state next : State C F) (run : cutStateOpt live state = some next) :
    next.stack = state.stack ∧ next.handler = state.handler := by
  cases live with
  | none =>
    simp only [cutStateOpt, Option.some.injEq] at run
    subst run
    exact ⟨rfl, rfl⟩
  | some names =>
    simp only [cutStateOpt, cutState, Option.map_eq_some_iff] at run
    obtain ⟨env, _, hnext⟩ := run
    subst hnext
    exact ⟨rfl, rfl⟩

/-- The `Assign` case. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem stackLocalsSwap_assign {C F : Type} (dest : Nat) (op : ClosLang.Op)
    (names : List Nat) (live : Option NumSet) (state : State C F) :
    StackLocalsSwapAt (.assign dest op names live) state := by
  intro res next run
  by_cases needs : (DataLang.opRequiresNames op == live.isNone) = true
  · simp only [evaluate, needs, typeError] at run ⊢
    obtain ⟨rfl, rfl⟩ := run
    trivial
  · have needsFalse : (DataLang.opRequiresNames op == live.isNone) = false := by
      simpa using needs
    simp only [evaluate, needsFalse] at run ⊢
    cases vars : DataSem.getVars names state.locals with
    | none =>
      simp only [vars, typeError] at run
      obtain ⟨rfl, rfl⟩ := run
      trivial
    | some values =>
      simp only [vars] at run
      cases cut : cutStateOpt live state with
      | none =>
        simp only [cut, typeError] at run
        obtain ⟨rfl, rfl⟩ := run
        trivial
      | some mid =>
        simp only [cut] at run
        cases app : doApp op values mid with
        | err error =>
          simp only [app] at run
          have resEq : res = some (.err error) := by
            simpa using (congrArg Prod.fst run).symm
          have nextEq : next = flushState true (installSfs op mid) := by
            simpa using (congrArg Prod.snd run).symm
          subst resEq
          subst nextEq
          rcases doApp_err op values mid error app with htype | ⟨name, outcome, opEq, errorEq⟩
          · subst htype
            trivial
          · subst errorEq
            constructor
            · simp only [flushState, if_true]
            · intro xs lsz len
              refine ⟨some 0, (flushState true (installSfs op mid)).safeForSpace,
                mid.stackMax, mid.peakHeapLength, ?_⟩
              simp only [Bool.false_eq_true, if_false,
                cutStateOpt_swapStackLocals_val live state xs lsz mid cut,
                doApp_swapStackLocals_err op values mid xs lsz (.abort (.ffiError outcome)) app]
              rfl
        | val pair =>
          obtain ⟨value, last⟩ := pair
          simp only [app] at run
          have resEq : res = none := by
            simpa using (congrArg Prod.fst run).symm
          have nextEq : next = setVar dest value (installSfs op last) := by
            simpa using (congrArg Prod.snd run).symm
          subst resEq
          subst nextEq
          have control := doApp_const op values mid value last app
          obtain ⟨cutStack, cutHandler⟩ := cutStateOpt_stack_handler live state mid cut
          refine ⟨?_, ?_, ?_⟩
          · simp only [setVar, installSfs]
            exact control.1.trans cutStack
          · simp only [setVar, installSfs]
            exact control.2.1.trans cutHandler
          · intro xs lsz len
            obtain ⟨sfs1, smx1, phl1, appVal⟩ :=
              doApp_swapStackLocals_val op values mid xs lsz value last app
            refine ⟨lsz, (installSfs op { last with
                stack := xs
                localsSize := lsz
                safeForSpace := sfs1
                stackMax := smx1
                peakHeapLength := phl1 }).safeForSpace, smx1, phl1, ?_⟩
            simp only [Bool.false_eq_true, if_false,
              cutStateOpt_swapStackLocals_val live state xs lsz mid cut, appVal]
            rfl

/-- Every program satisfies the stack-and-locals replacement property: the
    induction is HOL's `evaluate_ind` measure, clock first and program weight
    second. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem stackLocalsSwap_all {C F : Type} (program : DataLang.Prog)
    (state : State C F) :
    StackLocalsSwapAt program state := by
  refine clockWeightInduction (α := DataLang.Prog) (σ := State C F) (·.clock) sizeOf
    (motive := fun program state => StackLocalsSwapAt program state) ?_ program state
  intro program state exprIH smaller
  cases program with
  | skip => exact stackLocalsSwap_skip state
  | move dest src => exact stackLocalsSwap_move dest src state
  | assign dest op names live => exact stackLocalsSwap_assign dest op names live state
  | tick => exact stackLocalsSwap_tick state
  | makeSpace amount names => exact stackLocalsSwap_makeSpace amount names state
  | raise name => exact stackLocalsSwap_raise name state
  | «return» names => exact stackLocalsSwap_return names state
  | seq first second =>
    apply stackLocalsSwap_seq first second state
    · apply exprIH first state (by omega)
      simp only [DataLang.Prog.seq.sizeOf_spec]
      omega
    · intro mid bound
      apply exprIH second mid bound
      simp only [DataLang.Prog.seq.sizeOf_spec]
      omega
  | ifThenElse name yes no =>
    apply stackLocalsSwap_if name yes no state
    · apply exprIH yes state (by omega)
      simp only [DataLang.Prog.ifThenElse.sizeOf_spec]
      omega
    · apply exprIH no state (by omega)
      simp only [DataLang.Prog.ifThenElse.sizeOf_spec]
      omega
  | force ret label src =>
    cases ret with
    | none => exact stackLocalsSwap_tailForce label src state smaller
    | some ret =>
      obtain ⟨dest, live⟩ := ret
      exact stackLocalsSwap_returningForce dest live label src state smaller
  | call ret dest names handler =>
    cases ret with
    | none => exact stackLocalsSwap_tailCall dest names handler state smaller
    | some ret =>
      obtain ⟨returns, live⟩ := ret
      cases handler with
      | none =>
        exact stackLocalsSwap_returningCall_noHandler dest names returns live state smaller
      | some entry =>
        obtain ⟨handlerName, handlerBody⟩ := entry
        exact stackLocalsSwap_returningCall_handler dest names returns live state handlerName
          handlerBody smaller

/-- Replacing the stack by a list of the same length and replacing the locals
    size preserves the evaluation outcome, leaving only the resource
    observations free. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "evaluate_stack_and_locals_swap"]
theorem evaluate_stack_and_locals_swap {C F : Type} (program : DataLang.Prog)
    (state : State C F) :
    (match evaluate program state with
      | (some (.err (.abort .typeError)), _) => True
      | (some (.err (.abort a)), next) =>
        next.stack = [] ∧
          ∀ (xs : List Stack) (lsz : Option Nat), state.stack.length = xs.length →
            ∃ lss sfs smx phl,
              evaluate program { state with stack := xs, localsSize := lsz } =
                (some (.err (.abort a)),
                  { next with
                    localsSize := lss
                    safeForSpace := sfs
                    stackMax := smx
                    peakHeapLength := phl })
      | (some (.err (.raise t)), next) =>
        ∃ s2, jumpExc state = some s2 ∧ s2.locals = next.locals ∧
          s2.stack = next.stack ∧ s2.handler = next.handler ∧
          ∀ (xs : List Stack) (s7 : State C F) (lsz : Option Nat),
            jumpExc { state with stack := xs, localsSize := lsz } = some s7 ∧
              state.stack.length = xs.length →
              ∃ lss sfs smx phl,
                evaluate program { state with stack := xs, localsSize := lsz } =
                  (some (.err (.raise t)),
                    { next with
                      stack := s7.stack
                      handler := s7.handler
                      locals := s7.locals
                      localsSize := lss
                      safeForSpace := sfs
                      stackMax := smx
                      peakHeapLength := phl })
      | (res, next) =>
        next.stack = state.stack ∧ next.handler = state.handler ∧
          ∀ (xs : List Stack) (lsz : Option Nat), state.stack.length = xs.length →
            ∃ lss sfs smx phl,
              evaluate program { state with stack := xs, localsSize := lsz } =
                (res, { next with
                  localsSize := lss
                  stack := xs
                  safeForSpace := sfs
                  stackMax := smx
                  peakHeapLength := phl })) := by
  cases run : evaluate program state with
  | mk res next =>
    cases res with
    | none =>
      simp only []
      exact stackLocalsSwap_all program state none next run
    | some result =>
      cases result with
      | val values =>
        simp only []
        exact stackLocalsSwap_all program state (some (.val values)) next run
      | err error =>
        cases error with
        | abort a =>
          cases a with
          | typeError =>
            simp only []
          | timeoutError =>
            simp only []
            exact stackLocalsSwap_all program state
              (some (.err (.abort .timeoutError))) next run
          | ffiError event =>
            simp only []
            exact stackLocalsSwap_all program state
              (some (.err (.abort (.ffiError event)))) next run
        | raise t =>
          simp only []
          obtain ⟨s2, h2⟩ := stackLocalsSwap_all program state (some (.err (.raise t))) next run
          refine ⟨s2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, ?_⟩
          intro xs s7 lsz hprem
          obtain ⟨jumpedAt, len⟩ := hprem
          exact h2.2.2.2.2 xs s7 lsz jumpedAt len

/-- Replacing only the stack by a list of the same length preserves the
    evaluation outcome, leaving only the resource observations free. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "evaluate_stack_swap"]
theorem evaluate_stack_swap {C F : Type} (program : DataLang.Prog) (state : State C F) :
    (match evaluate program state with
      | (some (.err (.abort .typeError)), _) => True
      | (some (.err (.abort a)), next) =>
        next.stack = [] ∧
          ∀ (xs : List Stack), state.stack.length = xs.length →
            ∃ lss sfs smx phl,
              evaluate program { state with stack := xs } =
                (some (.err (.abort a)),
                  { next with
                    localsSize := lss
                    safeForSpace := sfs
                    stackMax := smx
                    peakHeapLength := phl })
      | (some (.err (.raise t)), next) =>
        ∃ s2, jumpExc state = some s2 ∧ s2.locals = next.locals ∧
          s2.stack = next.stack ∧ s2.handler = next.handler ∧
          ∀ (xs : List Stack) (s7 : State C F),
            jumpExc { state with stack := xs } = some s7 ∧ state.stack.length = xs.length →
              ∃ lss sfs smx phl,
                evaluate program { state with stack := xs } =
                  (some (.err (.raise t)),
                    { next with
                      stack := s7.stack
                      handler := s7.handler
                      locals := s7.locals
                      localsSize := lss
                      safeForSpace := sfs
                      stackMax := smx
                      peakHeapLength := phl })
      | (res, next) =>
        next.stack = state.stack ∧ next.handler = state.handler ∧
          ∀ (xs : List Stack), state.stack.length = xs.length →
            ∃ lss sfs smx phl,
              evaluate program { state with stack := xs } =
                (res, { next with
                  localsSize := lss
                  stack := xs
                  safeForSpace := sfs
                  stackMax := smx
                  peakHeapLength := phl })) := by
  cases run : evaluate program state with
  | mk res next =>
    have base := evaluate_stack_and_locals_swap program state
    rw [run] at base
    cases res with
    | none =>
      simp only [] at base ⊢
      obtain ⟨stackEq, handlerEq, hall⟩ := base
      refine ⟨stackEq, handlerEq, ?_⟩
      intro xs len
      exact hall xs state.localsSize len
    | some result =>
      cases result with
      | val values =>
        simp only [] at base ⊢
        obtain ⟨stackEq, handlerEq, hall⟩ := base
        refine ⟨stackEq, handlerEq, ?_⟩
        intro xs len
        exact hall xs state.localsSize len
      | err error =>
        cases error with
        | abort a =>
          cases a with
          | typeError =>
            simp only [] at base ⊢
          | timeoutError =>
            simp only [] at base ⊢
            obtain ⟨stackEmpty, hall⟩ := base
            refine ⟨stackEmpty, ?_⟩
            intro xs len
            exact hall xs state.localsSize len
          | ffiError event =>
            simp only [] at base ⊢
            obtain ⟨stackEmpty, hall⟩ := base
            refine ⟨stackEmpty, ?_⟩
            intro xs len
            exact hall xs state.localsSize len
        | raise t =>
          simp only [] at base ⊢
          obtain ⟨s2, h2⟩ := base
          refine ⟨s2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, ?_⟩
          intro xs s7 hprem
          obtain ⟨jumpedAt, len⟩ := hprem
          exact h2.2.2.2.2 xs s7 state.localsSize ⟨by simpa using jumpedAt, len⟩

/-- Replacing the stack by a list of the same length leaves the unwound frames
    unchanged, so the result's stack and handler are unchanged too. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "evaluate_stack"]
theorem evaluate_stack {C F : Type} (program : DataLang.Prog) (state : State C F) :
    (match evaluate program state with
      | (some (.err (.abort .typeError)), _) => True
      | (some (.err (.abort _)), next) => next.stack = []
      | (some (.err _), next) =>
        ∃ s2, jumpExc state = some s2 ∧ s2.locals = next.locals ∧
          s2.stack = next.stack ∧ s2.handler = next.handler
      | (_, next) => next.stack = state.stack ∧ next.handler = state.handler) := by
  cases run : evaluate program state with
  | mk res next =>
    have base := evaluate_stack_swap program state
    rw [run] at base
    cases res with
    | none =>
      simp only [] at base ⊢
      exact ⟨base.1, base.2.1⟩
    | some result =>
      cases result with
      | val values =>
        simp only [] at base ⊢
        exact ⟨base.1, base.2.1⟩
      | err error =>
        cases error with
        | abort a =>
          cases a with
          | typeError =>
            simp only [] at base ⊢
          | timeoutError =>
            simp only [] at base ⊢
            exact base.1
          | ffiError event =>
            simp only [] at base ⊢
            exact base.1
        | raise t =>
          simp only [] at base ⊢
          obtain ⟨s2, h2⟩ := base
          exact ⟨s2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1⟩

/-- A non-raising evaluation jumps to the state that differs from the starting
    state only in the frames the unwinding installs. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "evaluate_NONE_jump_exc"]
theorem evaluate_NONE_jump_exc {C F : Type} (program : DataLang.Prog) (state u1 x : State C F)
    (premise : evaluate program state = (none, u1) ∧ jumpExc u1 = some x) :
    jumpExc state = some { state with
      stack := x.stack
      handler := x.handler
      locals := x.locals
      localsSize := x.localsSize } := by
  obtain ⟨run, jumped⟩ := premise
  have base := evaluate_stack program state
  rw [run] at base
  simp only [] at base
  have stackEq : u1.stack = state.stack := base.1
  have handlerEq : u1.handler = state.handler := base.2
  unfold DataSem.jumpExc at jumped ⊢
  rw [stackEq, handlerEq] at jumped
  split
  · rename_i hlt
    split
    · rename_i size env handler rest heq
      rw [heq, if_pos hlt] at jumped
      simp only [Option.some.injEq] at jumped
      subst jumped
      rfl
    · rename_i hno
      rw [if_pos hlt] at jumped
      cases hdrop : List.drop (state.stack.length - (state.handler + 1)) state.stack with
      | nil =>
        rw [hdrop] at jumped
        exact absurd jumped (by simp)
      | cons frame rest =>
        cases frame with
        | env lsz env2 =>
          rw [hdrop] at jumped
          exact absurd jumped (by simp)
        | exc size env handler =>
          exact absurd hdrop (hno size env handler rest)
  · rename_i hge
    rw [if_neg hge] at jumped
    exact absurd jumped (by simp)

end Flapjack.Compiler.Backend.DataProps
