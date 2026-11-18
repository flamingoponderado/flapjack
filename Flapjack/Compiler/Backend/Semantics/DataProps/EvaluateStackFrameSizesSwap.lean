module

public import Flapjack.Compiler.Backend.Semantics.DataProps.EvaluateStackLocalsSwap
public import Flapjack.Compiler.Backend.Semantics.DataProps.StackFrameSizeRel
public import Flapjack.Compiler.Backend.Semantics.DataProps.CutFields
public import Flapjack.Compiler.Backend.Semantics.DataProps.FindCodeSize
public import Flapjack.Compiler.Backend.Semantics.DataProps.ResourceSwap
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.PermuteSwapStack
public import Flapjack.Misc.ClockWeightInduction

@[expose] public section

/-!
# Stack-frame-size replacement under data evaluation

Counterpart of `cakeml/compiler/backend/semantics/dataPropsScript.sml:2566`
`evaluate_swap_stack_frame_sizes_aux`, together with `evaluate_swap_local_sizes`
(`:2798`), `evaluate_swap_stack_frame_sizes` (`:2826`) and the consequences
`evaluate_stack_frame_sizes_FST` (`:2852`) and `evaluate_stack_frame_sizes_ffi`
(`:2862`).

The induction runs over a state relation rather than HOL's explicit list of
replaced fields: two states are related when they agree on every field the
evaluator reads except the locals size, the stack, the stack-frame sizes, and
the three resource observations, and their stacks agree frame by frame. That
relation is exactly the shape of HOL's conclusion, so the tagged theorem below
follows from the relation by unfolding it once.
-/

namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.DataSem

/-- Two states are related for the frame-size swap when the second is the first
    with the locals size, the stack, the stack-frame sizes, the stack maximum,
    the safety flag and the peak heap length replaced. -/
@[simp] private def FrameSwapState {C F : Type} (state other : State C F) : Prop :=
  other = { state with
    localsSize := other.localsSize
    stack := other.stack
    stackFrameSizes := other.stackFrameSizes
    stackMax := other.stackMax
    safeForSpace := other.safeForSpace
    peakHeapLength := other.peakHeapLength }

/-- The related state agrees on the locals. -/
private theorem frameSwapState_locals {C F : Type} {state other : State C F}
    (h : FrameSwapState state other) : other.locals = state.locals := by rw [h]

/-- The related state agrees on the global pointer. -/
private theorem frameSwapState_global {C F : Type} {state other : State C F}
    (h : FrameSwapState state other) : other.global = state.global := by rw [h]

/-- The related state agrees on the handler index. -/
private theorem frameSwapState_handler {C F : Type} {state other : State C F}
    (h : FrameSwapState state other) : other.handler = state.handler := by rw [h]

/-- The related state agrees on the references. -/
private theorem frameSwapState_refs {C F : Type} {state other : State C F}
    (h : FrameSwapState state other) : other.refs = state.refs := by rw [h]

/-- The related state agrees on the clock. -/
private theorem frameSwapState_clock {C F : Type} {state other : State C F}
    (h : FrameSwapState state other) : other.clock = state.clock := by rw [h]

/-- The related state agrees on the code map. -/
private theorem frameSwapState_code {C F : Type} {state other : State C F}
    (h : FrameSwapState state other) : other.code = state.code := by rw [h]

/-- The related state agrees on the FFI state. -/
private theorem frameSwapState_ffi {C F : Type} {state other : State C F}
    (h : FrameSwapState state other) : other.ffi = state.ffi := by rw [h]

/-- The related state agrees on the reserved space. -/
private theorem frameSwapState_space {C F : Type} {state other : State C F}
    (h : FrameSwapState state other) : other.space = state.space := by rw [h]

/-- The related state agrees on the timestamp counter. -/
private theorem frameSwapState_tstamps {C F : Type} {state other : State C F}
    (h : FrameSwapState state other) : other.tstamps = state.tstamps := by rw [h]

/-- The related state agrees on the limits. -/
private theorem frameSwapState_limits {C F : Type} {state other : State C F}
    (h : FrameSwapState state other) : other.limits = state.limits := by rw [h]

/-- The related state agrees on the compiler state. -/
private theorem frameSwapState_compile {C F : Type} {state other : State C F}
    (h : FrameSwapState state other) : other.compile = state.compile := by rw [h]

/-- The related state agrees on the compilation oracle. -/
private theorem frameSwapState_compileOracle {C F : Type} {state other : State C F}
    (h : FrameSwapState state other) : other.compileOracle = state.compileOracle := by rw [h]

/-- The frame-size swap property for one program and state: evaluating at any
    related state gives the same outcome, with a result state that is related in
    the same way and whose stack agrees frame by frame. -/
private def StackFrameSwapAt {C F : Type} (program : DataLang.Prog) (state : State C F) : Prop :=
  ∀ (res : Option (Result (List DataSem.Value) DataSem.Value)) (next : State C F)
    (other : State C F),
    evaluate program state = (res, next) →
    FrameSwapState state other →
    List.Forall₂ stackFrameSizeRel state.stack other.stack →
    ∃ other', evaluate program other = (res, other') ∧ FrameSwapState next other' ∧
      List.Forall₂ stackFrameSizeRel next.stack other'.stack

/-- Frame-size agreement is reflexive. Flapjack infrastructure toward the port
    of HOL `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem forall₂_stackFrameSizeRel_refl (frames : List Stack) :
    List.Forall₂ stackFrameSizeRel frames frames := by
  induction frames with
  | nil => exact List.Forall₂.nil
  | cons frame rest ih =>
    refine List.Forall₂.cons ?_ ih
    cases frame <;> simp [stackFrameSizeRel]

/-- The installation flag keeps the relation: it only updates the safety
    observation. Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem installSfs_frameSwap {C F : Type} (op : ClosLang.Op) {state other : State C F}
    (h : FrameSwapState state other) :
    FrameSwapState (installSfs op state) (installSfs op other) := by
  unfold installSfs
  rw [h]
  simp

/-- Assigning a local keeps the relation: only the locals change, and both
    states install the same binding. Flapjack infrastructure toward the port of
    HOL `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem setVar_frameSwap {C F : Type} (dest : Nat) (value : DataSem.Value)
    {state other : State C F} (h : FrameSwapState state other) :
    FrameSwapState (setVar dest value state) (setVar dest value other) := by
  unfold setVar
  rw [h]
  simp

/-- Flushing the state keeps the relation: it clears the locals, the locals size
    and the stack. Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem flushState_frameSwap {C F : Type} (all : Bool) {state other : State C F}
    (h : FrameSwapState state other) :
    FrameSwapState (flushState all state) (flushState all other) := by
  unfold flushState
  cases all with
  | false =>
    rw [h]
    simp
  | true =>
    rw [h]
    simp

/-- A successful primitive application at a related state succeeds with the same
    value and a related result state, whose stack agrees frame by frame.
    Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem doApp_frameSwap {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state other : State C F) (value : DataSem.Value) (next : State C F)
    (h : FrameSwapState state other) (rel : List.Forall₂ stackFrameSizeRel state.stack other.stack)
    (run : doApp op values state = .val (value, next)) :
    ∃ otherNext, doApp op values other = .val (value, otherNext) ∧ FrameSwapState next otherNext ∧
      List.Forall₂ stackFrameSizeRel next.stack otherNext.stack := by
  obtain ⟨safe, peak, mx, step1⟩ :=
    doApp_stackSafePeakSwap op values state value next other.stackMax other.safeForSpace
      other.peakHeapLength run
  obtain ⟨safe', peak', mx', step2⟩ :=
    doApp_lssStackFrameSwap op values
      { state with
        stackMax := other.stackMax
        safeForSpace := other.safeForSpace
        peakHeapLength := other.peakHeapLength }
      value { next with
        stackMax := mx
        safeForSpace := safe
        peakHeapLength := peak }
      other.localsSize other.stack other.stackFrameSizes step1
  have stackEq : next.stack = state.stack := (doApp_const op values state value next run).1
  rw [h]
  exact ⟨_, step2, rfl, by simpa [stackEq] using rel⟩

/-- A failed primitive application at a related state fails with the same error.
    Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem doApp_err_frameSwap {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state other : State C F) (error : Flapjack.SemanticPrimitivesHOL.ErrorResult DataSem.Value)
    (h : FrameSwapState state other) (run : doApp op values state = .err error) :
    doApp op values other = .err error := by
  have step1 := doApp_err_lssStackSafePeakSwap op values state error other.localsSize
    other.stackMax other.safeForSpace other.peakHeapLength run
  have step2 := doApp_err_lssStackFrameSwap op values
    { state with
      localsSize := other.localsSize
      stackMax := other.stackMax
      safeForSpace := other.safeForSpace
      peakHeapLength := other.peakHeapLength }
    error other.localsSize other.stack other.stackFrameSizes step1
  rw [h]
  exact step2

/-- Frame-size agreement decides the exception jump: when the original stack
    jumps to no frame, so does a related stack at the same handler index.
    Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem jumpExc_none_of_related {C F : Type} (state other : State C F)
    (handlerEq : other.handler = state.handler)
    (related : List.Forall₂ stackFrameSizeRel state.stack other.stack)
    (run : jumpExc state = none) : jumpExc other = none := by
  cases otherJump : jumpExc other with
  | none => rfl
  | some jumped =>
    obtain ⟨_, n, e, ls, xs1, lastNO, _⟩ := jumpExcImp other jumped otherJump
    rw [handlerEq] at lastNO
    have hlen : state.stack.length = other.stack.length := related.length_eq
    have hltS : state.handler < state.stack.length := by omega
    have relLast := listRelLastN stackFrameSizeRel state.stack other.stack (state.handler + 1)
      ⟨by omega, related⟩
    rw [lastNO] at relLast
    obtain ⟨frame, rest, frameRel, _, lastEq⟩ := List.forall₂_cons_right_iff.mp relLast
    cases frame with
    | env size env => simp [stackFrameSizeRel] at frameRel
    | exc size env handler =>
      have jumpSome : jumpExc state =
          some { state with
                  handler := handler
                  locals := env
                  stack := rest
                  localsSize := size } := by
        unfold jumpExc
        rw [if_pos hltS, ← wordSemLastN_eq_drop, lastEq]
      rw [jumpSome] at run
      cases run

/-- A successful exception jump at a related state succeeds with a related
    result: the unwound frame carries the same environment and handler, and the
    remaining stack agrees frame by frame. Flapjack infrastructure toward the
    port of HOL `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem jumpExc_frameSwap {C F : Type} (state other jumped : State C F)
    (h : FrameSwapState state other)
    (related : List.Forall₂ stackFrameSizeRel state.stack other.stack)
    (run : jumpExc state = some jumped) :
    ∃ jumped', jumpExc other = some jumped' ∧ FrameSwapState jumped jumped' ∧
      List.Forall₂ stackFrameSizeRel jumped.stack jumped'.stack := by
  obtain ⟨hlt, n, e, ls, xs1, lastN, jumpedEq⟩ := jumpExcImp state jumped run
  have handlerEq := frameSwapState_handler h
  have hltX : state.handler < other.stack.length := by
    have hlen : state.stack.length = other.stack.length := related.length_eq
    omega
  have relLast := listRelLastN stackFrameSizeRel state.stack other.stack (state.handler + 1)
    ⟨by omega, related⟩
  rw [lastN] at relLast
  obtain ⟨frame, rest, frameRel, restRel, lastX⟩ := List.forall₂_cons_left_iff.mp relLast
  cases frame with
  | env size env => simp [stackFrameSizeRel] at frameRel
  | exc size env handler =>
    simp only [stackFrameSizeRel] at frameRel
    obtain ⟨envEq, handlerEq'⟩ := frameRel
    subst envEq
    subst handlerEq'
    subst jumpedEq
    have jumpSwap :
        jumpExc other =
          some { other with
                  localsSize := size
                  stack := rest
                  handler := n
                  locals := e } := by
      unfold jumpExc
      rw [handlerEq, if_pos hltX, ← wordSemLastN_eq_drop, lastX]
    refine ⟨_, jumpSwap, ?_, restRel⟩
    rw [h]
    simp

/-- Pushing an environment frame at a related state keeps the relation: the
    pushed frame carries the same environment, and the stacks stay related.
    Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem pushEnv_frameSwap {C F : Type} (env : Spt DataSem.Value) (handler : Bool)
    (state other : State C F) (h : FrameSwapState state other)
    (related : List.Forall₂ stackFrameSizeRel state.stack other.stack) :
    FrameSwapState (DataSem.pushEnv env handler state) (DataSem.pushEnv env handler other) ∧
      List.Forall₂ stackFrameSizeRel (DataSem.pushEnv env handler state).stack
        (DataSem.pushEnv env handler other).stack := by
  have handlerEq := frameSwapState_handler h
  constructor
  · unfold DataSem.pushEnv
    rw [h]
    cases handler with
    | false => simp
    | true => simp [related.length_eq.symm]
  · unfold DataSem.pushEnv
    rw [h]
    cases handler with
    | false =>
      refine List.Forall₂.cons ?_ related
      simp [stackFrameSizeRel]
    | true =>
      refine List.Forall₂.cons ?_ related
      simp [stackFrameSizeRel]

/-- Restoring a saved environment at a related state keeps the relation: the
    popped frame carries the same environment and handler, and the remaining
    stacks stay related. Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem popEnv_frameSwap {C F : Type} (state other next : State C F)
    (h : FrameSwapState state other)
    (related : List.Forall₂ stackFrameSizeRel state.stack other.stack)
    (run : DataSem.popEnv state = some next) :
    ∃ next', DataSem.popEnv other = some next' ∧ FrameSwapState next next' ∧
      List.Forall₂ stackFrameSizeRel next.stack next'.stack := by
  cases stackEq : state.stack with
  | nil => simp [DataSem.popEnv, stackEq] at run
  | cons frame rest =>
    have rel' : List.Forall₂ stackFrameSizeRel (frame :: rest) other.stack := by
      rw [← stackEq]
      exact related
    obtain ⟨otherFrame, otherRest, frameRel, restRel, otherEq⟩ :=
      List.forall₂_cons_left_iff.mp rel'
    cases frame with
    | env size env =>
      cases otherFrame with
      | env otherSize otherEnv =>
        simp only [stackFrameSizeRel] at frameRel
        subst frameRel
        simp only [DataSem.popEnv, stackEq] at run
        obtain ⟨rfl⟩ := Option.some.inj run
        refine ⟨{ other with
            locals := env
            stack := otherRest
            localsSize := otherSize }, ?_, ?_, ?_⟩
        · simp only [DataSem.popEnv, otherEq]
        · rw [h]
          simp
        · exact restRel
      | exc otherSize otherEnv otherHandler => simp [stackFrameSizeRel] at frameRel
    | exc size env saved =>
      cases otherFrame with
      | env otherSize otherEnv => simp [stackFrameSizeRel] at frameRel
      | exc otherSize otherEnv otherHandler =>
        simp only [stackFrameSizeRel] at frameRel
        obtain ⟨envEq, savedEq⟩ := frameRel
        subst envEq
        subst savedEq
        simp only [DataSem.popEnv, stackEq] at run
        obtain ⟨rfl⟩ := Option.some.inj run
        refine ⟨{ other with
            locals := env
            stack := otherRest
            localsSize := otherSize
            handler := saved }, ?_, ?_, ?_⟩
        · simp only [DataSem.popEnv, otherEq]
        · rw [h]
          simp
        · exact restRel

/-- Entering a call at a related state keeps the relation: the locals become the
    same argument list, the locals size and the resource observations are free.
    Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem callEnv_frameSwap {C F : Type} (args : List DataSem.Value)
    (size otherSize : Option Nat)
    (state other : State C F) (h : FrameSwapState state other) :
    FrameSwapState (DataSem.callEnv args size state) (DataSem.callEnv args otherSize other) := by
  unfold DataSem.callEnv
  rw [h]
  simp

/-- The narrow cut keeps the relation: it reads only the locals and installs the
    same environment. Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem cutStateOpt_frameSwap {C F : Type} (live : Option NumSet)
    (state other next : State C F)
    (h : FrameSwapState state other) (cut : cutStateOpt live state = some next) :
    ∃ otherNext, cutStateOpt live other = some otherNext ∧ FrameSwapState next otherNext := by
  cases live with
  | none =>
    simp only [cutStateOpt, Option.some.injEq] at cut
    subst cut
    exact ⟨other, by simp [cutStateOpt], h⟩
  | some names =>
    simp only [cutStateOpt, cutState, Option.map_eq_some_iff] at cut
    obtain ⟨env, envEq, nextEq⟩ := cut
    subst nextEq
    refine ⟨{ other with locals := env }, ?_, ?_⟩
    · simp [cutStateOpt, cutState, frameSwapState_locals h, envEq]
    · rw [h]
      simp

/-- Clamping the clock keeps the relation, because both runs agree on the clocks.
    Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem fixClock_frameSwap {C F : Type} {state other : State C F}
    (result : Option (Result (List DataSem.Value) DataSem.Value)) (next otherNext : State C F)
    (h : FrameSwapState state other) (rel : FrameSwapState next otherNext) :
    FrameSwapState (fixClock state (result, next)).2 (fixClock other (result, otherNext)).2 := by
  have clockEq := frameSwapState_clock h
  have nextClockEq := frameSwapState_clock rel
  unfold fixClock
  rw [h, rel]
  simp

/-- The `Skip` case. Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem stackFrameSwap_skip {C F : Type} (state : State C F) :
    StackFrameSwapAt (.skip : DataLang.Prog) state := by
  intro res next other run h rel
  simp only [evaluate, Prod.mk.injEq] at run
  obtain ⟨rfl, rfl⟩ := run
  exact ⟨other, by simp [evaluate], h, rel⟩

/-- The `Move` case. Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem stackFrameSwap_move {C F : Type} (dest src : Nat) (state : State C F) :
    StackFrameSwapAt (.move dest src) state := by
  intro res next other run h rel
  have localsEq := frameSwapState_locals h
  cases read : getVar src state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨other, ?_, h, rel⟩
    simp [evaluate, typeError, localsEq, read]
  | some value =>
    simp only [evaluate, read, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨setVar dest value other, ?_, ?_, ?_⟩
    · simp [evaluate, localsEq, read]
    · rw [h]
      simp [setVar]
    · simpa [setVar] using rel

/-- The `Tick` case. Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem stackFrameSwap_tick {C F : Type} (state : State C F) :
    StackFrameSwapAt (.tick : DataLang.Prog) state := by
  intro res next other run h rel
  have clockEq := frameSwapState_clock h
  by_cases zero : state.clock = 0
  · simp only [evaluate, zero, timeoutError] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨flushState true other, ?_, ?_, ?_⟩
    · simp [evaluate, timeoutError, clockEq, if_pos zero]
    · rw [h]
      simp [flushState]
    · simp [flushState]
  · simp only [evaluate, zero] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨decClock other, ?_, ?_, ?_⟩
    · simp [evaluate, clockEq, if_neg zero]
    · rw [h]
      simp [decClock]
    · simpa [decClock] using rel

/-- The `MakeSpace` case. Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem stackFrameSwap_makeSpace {C F : Type} (amount : Nat) (names : NumSet)
    (state : State C F) : StackFrameSwapAt (.makeSpace amount names) state := by
  intro res next other run h rel
  have localsEq := frameSwapState_locals h
  cases cut : cutEnv names state.locals with
  | none =>
    simp only [evaluate, cut, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨other, ?_, h, rel⟩
    simp [evaluate, typeError, localsEq, cut]
  | some env =>
    simp only [evaluate, cut, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨addSpace { other with locals := env } amount, ?_, ?_, ?_⟩
    · simp [evaluate, localsEq, cut]
    · rw [h]
      simp [addSpace]
    · simpa [addSpace] using rel

/-- The `Return` case. Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem stackFrameSwap_return {C F : Type} (names : List Nat) (state : State C F) :
    StackFrameSwapAt (.return names) state := by
  intro res next other run h rel
  have localsEq := frameSwapState_locals h
  cases read : DataSem.getVars names state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨other, ?_, h, rel⟩
    simp [evaluate, typeError, localsEq, read]
  | some values =>
    simp only [evaluate, read, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨flushState false other, ?_, ?_, ?_⟩
    · simp [evaluate, localsEq, read]
    · rw [h]
      simp [flushState]
    · simpa [flushState] using rel

/-- The `If` case. Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem stackFrameSwap_if {C F : Type} (name : Nat) (yes no : DataLang.Prog)
    (state : State C F) (yesIH : StackFrameSwapAt yes state) (noIH : StackFrameSwapAt no state) :
    StackFrameSwapAt (.ifThenElse name yes no) state := by
  intro res next other run h rel
  have localsEq := frameSwapState_locals h
  cases read : getVar name state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨other, ?_, h, rel⟩
    simp [evaluate, typeError, localsEq, read]
  | some value =>
    by_cases yesValue : isBool true value
    · have branch : evaluate yes state = (res, next) := by
        simpa [evaluate, read, yesValue] using run
      simpa [evaluate, localsEq, read, yesValue] using yesIH res next other branch h rel
    · by_cases noValue : isBool false value
      · have branch : evaluate no state = (res, next) := by
          simpa [evaluate, read, yesValue, noValue] using run
        simpa [evaluate, localsEq, read, yesValue, noValue] using noIH res next other branch h rel
      · simp only [evaluate, read, yesValue, noValue, typeError] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨other, ?_, h, rel⟩
        simp [evaluate, typeError, localsEq, read, yesValue, noValue]

/-- A sequential composition whose first half has stopped returns the first
    half's result. Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem seq_some {C F : Type} (first second : DataLang.Prog) (state : State C F)
    (stopped : Result (List DataSem.Value) DataSem.Value) (next : State C F)
    (run : evaluate first state = (some stopped, next)) :
    evaluate (.seq first second) state = (some stopped, next) := by
  have bound : next.clock ≤ state.clock := by simpa only [run] using evaluate_clock_le first state
  simp only [evaluate, run, fixClock, Nat.min_eq_right bound]

/-- A sequential composition whose first half continues evaluates the second
    half at the first half's result state. Flapjack infrastructure toward the
    port of HOL `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem seq_none {C F : Type} (first second : DataLang.Prog) (state mid : State C F)
    (run : evaluate first state = (none, mid)) :
    evaluate (.seq first second) state = evaluate second mid := by
  have bound : mid.clock ≤ state.clock := by simpa only [run] using evaluate_clock_le first state
  simp only [evaluate, run, fixClock, Nat.min_eq_right bound]

/-- The `Seq` case. Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem stackFrameSwap_seq {C F : Type} (first second : DataLang.Prog)
    (state : State C F) (firstIH : StackFrameSwapAt first state)
    (secondIH : ∀ mid : State C F, mid.clock ≤ state.clock → StackFrameSwapAt second mid) :
    StackFrameSwapAt (.seq first second) state := by
  intro res next other run h rel
  cases firstRun : evaluate first state with
  | mk outcome mid =>
    have midClock : mid.clock ≤ state.clock := by
      simpa only [firstRun] using evaluate_clock_le first state
    obtain ⟨midOther, firstOther, relMid, stackMid⟩ :=
      firstIH outcome mid other firstRun h rel
    cases outcome with
    | some stopped =>
      have clamp : fixClock state (evaluate first state) = (some stopped, mid) := by
        rw [fixClockEvaluate, firstRun]
      have hres : res = some stopped := by
        have hh := congrArg Prod.fst run
        simpa only [evaluate, clamp] using hh.symm
      have hnext : next = mid := by
        have hh := congrArg Prod.snd run
        simpa only [evaluate, clamp] using hh.symm
      rw [hres, hnext]
      refine ⟨midOther, ?_, relMid, stackMid⟩
      rw [seq_some first second other stopped midOther firstOther]
    | none =>
      have secondRun : evaluate second mid = (res, next) := by
        have clamp : fixClock state (evaluate first state) = (none, mid) := by
          rw [fixClockEvaluate, firstRun]
        simpa only [evaluate, clamp] using run
      obtain ⟨lastOther, secondOther, relLast, stackLast⟩ :=
        secondIH mid midClock res next midOther secondRun relMid stackMid
      refine ⟨lastOther, ?_, relLast, stackLast⟩
      rw [seq_none first second other midOther firstOther]
      exact secondOther

/-- The `Assign` case. Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem stackFrameSwap_assign {C F : Type} (dest : Nat) (op : ClosLang.Op)
    (names : List Nat) (live : Option NumSet) (state : State C F) :
    StackFrameSwapAt (.assign dest op names live) state := by
  intro res next other run h rel
  have localsEq := frameSwapState_locals h
  by_cases needs : (DataLang.opRequiresNames op == live.isNone) = true
  · simp only [evaluate, needs, typeError] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨other, by simp [evaluate, needs], h, rel⟩
  · have needsFalse : (DataLang.opRequiresNames op == live.isNone) = false := by simpa using needs
    simp only [evaluate, needsFalse] at run
    cases vars : DataSem.getVars names state.locals with
    | none =>
      simp only [vars, typeError] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨other, ?_, h, rel⟩
      simp [evaluate, typeError, needsFalse, localsEq, vars]
    | some values =>
      simp only [vars] at run
      have varsOther : DataSem.getVars names other.locals = some values := by
        rw [localsEq]
        exact vars
      cases cut : cutStateOpt live state with
      | none =>
        simp only [cut, typeError] at run
        obtain ⟨rfl, rfl⟩ := run
        have cutOther : cutStateOpt live other = none := by
          cases live with
          | none => simp [cutStateOpt] at cut
          | some names =>
            cases envEq : cutEnv names state.locals with
            | none =>
              simp only [cutStateOpt, cutState, envEq] at cut ⊢
              rw [frameSwapState_locals h, envEq]
              rfl
            | some env =>
              simp only [cutStateOpt, cutState, envEq] at cut
              simp at cut
        refine ⟨other, ?_, h, rel⟩
        simp [evaluate, typeError, needsFalse, varsOther, cutOther]
      | some mid =>
        simp only [cut] at run
        obtain ⟨midOther, cutOtherRun, relMid⟩ := cutStateOpt_frameSwap live state other mid h cut
        cases app : doApp op values mid with
        | err error =>
          simp only [app] at run
          obtain ⟨rfl, rfl⟩ := run
          have appOther := doApp_err_frameSwap op values mid midOther error relMid app
          refine ⟨flushState true (installSfs op midOther), ?_, ?_, ?_⟩
          · simp [evaluate, needsFalse, varsOther, cutOtherRun, appOther]
          · exact flushState_frameSwap true (installSfs_frameSwap op relMid)
          · simp [flushState]
        | val pair =>
          obtain ⟨value, last⟩ := pair
          simp only [app] at run
          obtain ⟨rfl, rfl⟩ := run
          obtain ⟨lastOther, appOther, relLast, stackLast⟩ :=
            doApp_frameSwap op values mid midOther value last relMid
              (by
                rw [cutStateOpt_stack live state mid cut,
                  cutStateOpt_stack live other midOther cutOtherRun]
                exact rel) app
          refine ⟨setVar dest value (installSfs op lastOther), ?_, ?_, ?_⟩
          · simp [evaluate, needsFalse, varsOther, cutOtherRun, appOther]
          · exact setVar_frameSwap dest value (installSfs_frameSwap op relLast)
          · simpa [setVar, installSfs] using stackLast

/-- The `Raise` case. Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem stackFrameSwap_raise {C F : Type} (name : Nat) (state : State C F) :
    StackFrameSwapAt (.raise name) state := by
  intro res next other run h rel
  have localsEq := frameSwapState_locals h
  cases read : getVar name state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨other, ?_, h, rel⟩
    simp [evaluate, typeError, localsEq, read]
  | some value =>
    cases jump : jumpExc state with
    | none =>
      simp only [evaluate, read, jump, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      have jumpOther := jumpExc_none_of_related state other (frameSwapState_handler h) rel jump
      refine ⟨other, ?_, h, rel⟩
      simp [evaluate, typeError, localsEq, read, jumpOther]
    | some jumped =>
      simp only [evaluate, read, jump, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      obtain ⟨jumpedOther, jumpOther, relJump, stackJump⟩ :=
        jumpExc_frameSwap state other jumped h rel jump
      exact ⟨jumpedOther, by simp [evaluate, localsEq, read, jumpOther], relJump, stackJump⟩

/-- Clearing the stack and the locals keeps the relation. Flapjack
    infrastructure toward the port of HOL `evaluate_swap_stack_frame_sizes_aux`;
    no separate HOL original. -/
private theorem clearState_frameSwap {C F : Type} {state other : State C F}
    (h : FrameSwapState state other) :
    FrameSwapState { state with stack := [], locals := .ln }
      { other with stack := [], locals := .ln } := by
  rw [h]
  simp

/-- Assigning several locals keeps the relation: only the locals change, and
    both states install the same bindings. Flapjack infrastructure toward the
    port of HOL `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem setVars_frameSwap {C F : Type} (names : List Nat) (values : List DataSem.Value)
    {state other : State C F} (h : FrameSwapState state other) :
    FrameSwapState (setVars names values state) (setVars names values other) := by
  unfold setVars
  rw [h]
  simp

/-- The `Force` case without a destination: the thunk is forced in place or the
    called body runs at the call state, whose frame size comes from the swapped
    frame-size map. Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem stackFrameSwap_tailForce {C F : Type} (label src : Nat) (state : State C F)
    (bodyIH : ∀ (body : DataLang.Prog) (called : State C F),
      called.clock < state.clock → StackFrameSwapAt body called) :
    StackFrameSwapAt (.force none label src) state := by
  intro res next other run h rel
  have localsEq := frameSwapState_locals h
  have refsEq := frameSwapState_refs h
  have clockEq := frameSwapState_clock h
  have codeEq := frameSwapState_code h
  cases read : getVar src state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨other, ?_, h, rel⟩
    simp [evaluate, typeError, localsEq, read]
  | some thunk =>
    cases th : destThunk thunk state.refs with
    | badRef =>
      simp only [evaluate, read, th, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨other, ?_, h, rel⟩
      simp [evaluate, typeError, localsEq, read, refsEq, th]
    | notThunk =>
      simp only [evaluate, read, th, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨other, ?_, h, rel⟩
      simp [evaluate, typeError, localsEq, read, refsEq, th]
    | isThunk mode value =>
      cases mode with
      | evaluated =>
        simp only [evaluate, read, th, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨flushState false other, ?_, ?_, ?_⟩
        · simp [evaluate, localsEq, read, refsEq, th]
        · exact flushState_frameSwap false h
        · simpa [flushState] using rel
      | notEvaluated =>
        cases found : findCode (some label) [thunk, value] state.code state.stackFrameSizes with
        | none =>
          obtain ⟨_, foundOther⟩ := findCode_size_upto (some label) [thunk, value] state.code
            state.stackFrameSizes other.stackFrameSizes none found
          simp only [evaluate, read, th, found, typeError, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨other, ?_, h, rel⟩
          simp [evaluate, typeError, localsEq, read, refsEq, th, codeEq, foundOther]
        | some foundEntry =>
          obtain ⟨otherSize, foundOther⟩ := findCode_size_upto (some label) [thunk, value]
            state.code state.stackFrameSizes other.stackFrameSizes foundEntry found
          obtain ⟨args, body, size⟩ := foundEntry
          have foundOther' : findCode (some label) [thunk, value] state.code other.stackFrameSizes =
              some (args, body, otherSize) := by simpa using foundOther
          by_cases zero : state.clock = 0
          · simp only [evaluate, read, th, found, zero, timeoutError] at run
            obtain ⟨rfl, rfl⟩ := run
            refine ⟨{ other with stack := [], locals := .ln }, ?_, ?_, ?_⟩
            · simp [evaluate, timeoutError, localsEq, read, refsEq, th, codeEq, foundOther',
                clockEq, if_pos zero]
            · simpa [zero] using clearState_frameSwap h
            · exact List.Forall₂.nil
          · let called := DataSem.callEnv args size (DataSem.decClock state)
            let calledOther := DataSem.callEnv args otherSize (DataSem.decClock other)
            have clockLt : called.clock < state.clock := by
              simp only [called, DataSem.callEnv, DataSem.decClock]
              omega
            have relClock : FrameSwapState (DataSem.decClock state) (DataSem.decClock other) := by
              rw [h]
              simp [DataSem.decClock]
            have relCall : FrameSwapState called calledOther :=
              callEnv_frameSwap args size otherSize (DataSem.decClock state)
                (DataSem.decClock other) relClock
            have stackCall : List.Forall₂ stackFrameSizeRel called.stack calledOther.stack := by
              simpa [called, calledOther, DataSem.callEnv, DataSem.decClock] using rel
            cases bodyRun : evaluate body called with
            | mk outcome last =>
              obtain ⟨lastOther, bodyOther, relBody, stackBody⟩ :=
                bodyIH body called clockLt outcome last calledOther bodyRun relCall stackCall
              have bodyRun' :
                  evaluate body (DataSem.callEnv args size (DataSem.decClock state)) =
                    (outcome, last) := bodyRun
              have bodyOther' :
                  evaluate body (DataSem.callEnv args otherSize (DataSem.decClock other)) =
                    (outcome, lastOther) := bodyOther
              simp only [evaluate, read, th, found, zero] at run
              rw [bodyRun'] at run
              cases outcome with
              | none =>
                simp only [typeError] at run
                obtain ⟨rfl, rfl⟩ := run
                refine ⟨lastOther, ?_, relBody, stackBody⟩
                simp only [evaluate, localsEq, read, refsEq, th, codeEq, foundOther', clockEq,
                  if_neg zero, bodyOther', typeError]
              | some stopped =>
                obtain ⟨rfl, rfl⟩ := run
                refine ⟨lastOther, ?_, relBody, stackBody⟩
                simp only [evaluate, localsEq, read, refsEq, th, codeEq, foundOther', clockEq,
                  if_neg zero, bodyOther']

/-- Frame-size agreement decides frame restoration: when the original stack has
    no frame to restore, neither does a related stack. Flapjack infrastructure
    toward the port of HOL `evaluate_swap_stack_frame_sizes_aux`; no separate HOL
    original. -/
private theorem popEnv_none_of_related {C F : Type} (state other : State C F)
    (related : List.Forall₂ stackFrameSizeRel state.stack other.stack)
    (run : DataSem.popEnv state = none) : DataSem.popEnv other = none := by
  cases stackEq : state.stack with
  | nil =>
    have otherNil : other.stack = [] := by
      have empty := related
      rw [stackEq] at empty
      simpa using List.forall₂_nil_left_iff.mp empty
    simp [DataSem.popEnv, otherNil]
  | cons frame rest =>
    simp only [DataSem.popEnv, stackEq] at run
    cases frame <;> simp at run

/-- The `Force` case with a destination: forcing an evaluated thunk stores the
    value in place, and forcing an unevaluated one runs the body, restores the
    frame and stores the result. Flapjack infrastructure toward the port of HOL
    `evaluate_swap_stack_frame_sizes_aux`; no separate HOL original. -/
private theorem stackFrameSwap_returningForce {C F : Type} (dest : Nat) (live : NumSet)
    (label src : Nat) (state : State C F)
    (bodyIH : ∀ (body : DataLang.Prog) (called : State C F),
      called.clock < state.clock → StackFrameSwapAt body called) :
    StackFrameSwapAt (.force (some (dest, live)) label src) state := by
  intro res next other run h rel
  have localsEq := frameSwapState_locals h
  have refsEq := frameSwapState_refs h
  have clockEq := frameSwapState_clock h
  have codeEq := frameSwapState_code h
  cases read : getVar src state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨other, ?_, h, rel⟩
    simp [evaluate, typeError, localsEq, read]
  | some thunk =>
    cases th : destThunk thunk state.refs with
    | badRef =>
      simp only [evaluate, read, th, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨other, ?_, h, rel⟩
      simp [evaluate, typeError, localsEq, read, refsEq, th]
    | notThunk =>
      simp only [evaluate, read, th, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨other, ?_, h, rel⟩
      simp [evaluate, typeError, localsEq, read, refsEq, th]
    | isThunk mode value =>
      cases mode with
      | evaluated =>
        cases cut : cutEnv live state.locals with
        | none =>
          simp only [evaluate, read, th, cut, typeError, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨other, ?_, h, rel⟩
          simp [evaluate, typeError, localsEq, read, refsEq, th, cut]
        | some env =>
          have cutOther : cutEnv live other.locals = some env := by
            rw [localsEq]
            exact cut
          simp only [evaluate, read, th, cut, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨setVar dest value { other with locals := env }, ?_, ?_, ?_⟩
          · simp [evaluate, localsEq, read, refsEq, th, cut]
          · exact setVar_frameSwap dest value (by rw [h]; simp)
          · simpa [setVar] using rel
      | notEvaluated =>
        cases found : findCode (some label) [thunk, value] state.code state.stackFrameSizes with
        | none =>
          obtain ⟨_, foundOther⟩ := findCode_size_upto (some label) [thunk, value] state.code
            state.stackFrameSizes other.stackFrameSizes none found
          simp only [evaluate, read, th, found, typeError, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨other, ?_, h, rel⟩
          simp [evaluate, typeError, localsEq, read, refsEq, th, codeEq, foundOther]
        | some foundEntry =>
          obtain ⟨otherSize, foundOther⟩ := findCode_size_upto (some label) [thunk, value]
            state.code state.stackFrameSizes other.stackFrameSizes foundEntry found
          obtain ⟨args, body, size⟩ := foundEntry
          have foundOther' : findCode (some label) [thunk, value] state.code other.stackFrameSizes =
              some (args, body, otherSize) := by simpa using foundOther
          cases cut : cutEnv live state.locals with
          | none =>
            simp only [evaluate, read, th, found, cut, typeError, Prod.mk.injEq] at run
            obtain ⟨rfl, rfl⟩ := run
            refine ⟨other, ?_, h, rel⟩
            simp [evaluate, typeError, localsEq, read, refsEq, th, codeEq, foundOther', cut]
          | some env =>
            have cutOther : cutEnv live other.locals = some env := by
              rw [localsEq]
              exact cut
            by_cases zero : state.clock = 0
            · simp only [evaluate, read, th, found, cut, zero, timeoutError] at run
              obtain ⟨rfl, rfl⟩ := run
              let callState :=
                DataSem.callEnv args size (DataSem.pushEnv env false (DataSem.decClock state))
              let callOther :=
                DataSem.callEnv args otherSize (DataSem.pushEnv env false (DataSem.decClock other))
              have relPush := pushEnv_frameSwap env false (DataSem.decClock state)
                (DataSem.decClock other) (by rw [h]; simp [DataSem.decClock]) rel
              have relCall : FrameSwapState callState callOther :=
                callEnv_frameSwap args size otherSize _ _ relPush.1
              refine ⟨{ callOther with stack := [], locals := .ln }, ?_, ?_, ?_⟩
              · simp [evaluate, timeoutError, localsEq, read, refsEq, th, codeEq, foundOther',
                  clockEq, cut, callOther, if_pos zero]
              · simpa [zero, callState, callOther] using clearState_frameSwap relCall
              · exact List.Forall₂.nil
            · let callState :=
                DataSem.callEnv args size (DataSem.pushEnv env false (DataSem.decClock state))
              let callOther :=
                DataSem.callEnv args otherSize (DataSem.pushEnv env false (DataSem.decClock other))
              have clockLt : callState.clock < state.clock := by
                simp only [callState, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock]
                omega
              have relPush := pushEnv_frameSwap env false (DataSem.decClock state)
                (DataSem.decClock other) (by rw [h]; simp [DataSem.decClock]) rel
              have relCall : FrameSwapState callState callOther :=
                callEnv_frameSwap args size otherSize _ _ relPush.1
              have stackCall : List.Forall₂ stackFrameSizeRel callState.stack callOther.stack := by
                simpa [callState, callOther, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock]
                  using relPush.2
              cases bodyRun : evaluate body callState with
              | mk outcome last =>
                obtain ⟨lastOther, bodyOther, relBody, stackBody⟩ :=
                  bodyIH body callState clockLt outcome last callOther bodyRun relCall stackCall
                have bodyRun' :
                    evaluate body
                        (DataSem.callEnv args size
                          (DataSem.pushEnv env false (DataSem.decClock state))) =
                      (outcome, last) := bodyRun
                have bodyOther' :
                    evaluate body
                        (DataSem.callEnv args otherSize
                          (DataSem.pushEnv env false (DataSem.decClock other))) =
                      (outcome, lastOther) := bodyOther
                have relClamp : FrameSwapState
                    { last with clock := min callState.clock last.clock }
                    { lastOther with clock := min callOther.clock lastOther.clock } :=
                  fixClock_frameSwap outcome last lastOther relCall relBody
                have stackClamp : List.Forall₂ stackFrameSizeRel
                    ({ last with clock := min callState.clock last.clock } : State C F).stack
                    ({ lastOther with clock := min callOther.clock lastOther.clock } :
                      State C F).stack := by simpa using stackBody
                simp only [evaluate, read, th, found, cut, zero] at run
                rw [bodyRun'] at run
                have clampEq :
                    (fixClock callState (outcome, last)).2 =
                      ({ last with clock := min callState.clock last.clock } : State C F) := rfl
                rw [clampEq] at run
                cases outcome with
                | none =>
                  simp only [typeError] at run
                  obtain ⟨rfl, rfl⟩ := run
                  refine ⟨_, ?_, relClamp, stackClamp⟩
                  simp only [evaluate, localsEq, read, refsEq, th, codeEq, foundOther', clockEq,
                    cut, callOther, if_neg zero, bodyOther', fixClock, typeError]
                | some stopped =>
                  cases stopped with
                  | err error =>
                    obtain ⟨rfl, rfl⟩ := run
                    refine ⟨_, ?_, relClamp, stackClamp⟩
                    simp only [evaluate, localsEq, read, refsEq, th, codeEq, foundOther', clockEq,
                      cut, callOther, if_neg zero, bodyOther', fixClock]
                  | val values =>
                    cases values with
                    | nil =>
                      simp only [typeError] at run
                      obtain ⟨rfl, rfl⟩ := run
                      refine ⟨_, ?_, relClamp, stackClamp⟩
                      simp only [evaluate, localsEq, read, refsEq, th, codeEq, foundOther', clockEq,
                        cut, callOther, if_neg zero, bodyOther', fixClock, typeError]
                    | cons value rest =>
                      cases rest with
                      | cons otherValue tail =>
                        simp only [typeError] at run
                        obtain ⟨rfl, rfl⟩ := run
                        refine ⟨_, ?_, relClamp, stackClamp⟩
                        simp only [evaluate, localsEq, read, refsEq, th, codeEq, foundOther',
                          clockEq, cut, callOther, if_neg zero, bodyOther', fixClock, typeError]
                      | nil =>
                        cases pop : DataSem.popEnv
                            ({ last with clock := min callState.clock last.clock } : State C F) with
                        | none =>
                          simp only [pop, typeError] at run
                          obtain ⟨rfl, rfl⟩ := run
                          have popOtherNone := popEnv_none_of_related _ _ stackClamp pop
                          refine ⟨_, ?_, relClamp, stackClamp⟩
                          simp only [evaluate, localsEq, read, refsEq, th, codeEq, foundOther',
                            clockEq, cut, callOther, if_neg zero, bodyOther', fixClock,
                            popOtherNone, typeError]
                        | some popped =>
                          obtain ⟨poppedOther, popOther, relPopped, stackPopped⟩ :=
                            popEnv_frameSwap _ _ popped relClamp stackClamp pop
                          simp only [pop] at run
                          obtain ⟨rfl, rfl⟩ := run
                          refine ⟨setVar dest value poppedOther, ?_, ?_, ?_⟩
                          · simp only [evaluate, localsEq, read, refsEq, th, codeEq, foundOther',
                              clockEq, cut, callOther, if_neg zero, bodyOther', fixClock, popOther]
                          · exact setVar_frameSwap dest value relPopped
                          · simpa [setVar] using stackPopped

end Flapjack.Compiler.Backend.DataProps
