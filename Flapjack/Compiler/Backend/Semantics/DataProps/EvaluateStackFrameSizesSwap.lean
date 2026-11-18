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

end Flapjack.Compiler.Backend.DataProps
