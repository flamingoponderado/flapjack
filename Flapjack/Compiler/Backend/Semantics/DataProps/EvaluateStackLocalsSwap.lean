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
