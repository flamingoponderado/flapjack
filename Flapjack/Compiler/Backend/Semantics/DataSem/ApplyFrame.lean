module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
public import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyFields

@[expose] public section

/-! Control fields preserved by primitive application and evaluation. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- The execution fields needed by compiler-pass simulation. Resource
bookkeeping and values in the reference store are intentionally excluded. -/
def SameLocalControl {C F : Type} (before after : State C F) : Prop :=
  after.locals = before.locals ∧ after.stack = before.stack ∧
  after.handler = before.handler ∧ after.localsSize = before.localsSize ∧
  after.stackFrameSizes = before.stackFrameSizes ∧ after.clock = before.clock

/-- Control fields preserved even when a live-name cut changes locals. -/
def SameControl {C F : Type} (before after : State C F) : Prop :=
  after.stack = before.stack ∧ after.handler = before.handler ∧ after.localsSize = before.localsSize ∧
  after.stackFrameSizes = before.stackFrameSizes ∧ after.clock = before.clock

/-- Control preservation composes through sequential execution. -/
theorem SameControl.trans {C F : Type} {a b c : State C F}
    (first : SameControl a b) (second : SameControl b c) : SameControl a c := by
  rcases first with ⟨a1, a2, a3, a4, a5⟩
  rcases second with ⟨b1, b2, b3, b4, b5⟩
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5⟩

/-- Exception-handler availability depends only on stack and handler, both
of which are preserved by `SameControl`. -/
theorem SameControl.jumpExc_ne_none {C F : Type} {before after : State C F}
    (control : SameControl before after) (available : jumpExc before ≠ none) : jumpExc after ≠ none := by
  rcases control with ⟨stack, handler, _, _, _⟩
  by_cases h : before.handler < before.stack.length
  · simp only [jumpExc, stack, handler, ite_eq_left h] at available ⊢
    cases frame : before.stack.drop (before.stack.length - (before.handler + 1)) with
    | nil => simp [frame] at available
    | cons head rest => cases head <;> simp_all
  · simp [jumpExc, h] at available

/-- Successful space accounting preserves local and control fields. -/
theorem doSpace_frame {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : State C F) (run : doSpace op args state = some next) : SameLocalControl state next := by
  unfold doSpace at run
  split at run
  · simp only [Option.some.injEq] at run
    subst next
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · dsimp only at run
    split at run
    · simp only [Option.some.injEq] at run
      subst next
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp only [consumeSpace] at run
      split at run
      · simp at run
      · simp only [Option.some.injEq] at run
        subst next
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Auxiliary application preserves local control fields for every operation. -/
private theorem doAppAux_controlFrame {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux op args state = .val (value, next)) : SameLocalControl state next := by
  obtain ⟨stack, localsSize, _, _, locals, _, handler, clock, frameSizes, _⟩ :=
    doAppAux_fieldFrame op args state next value run
  exact ⟨locals, stack, handler, localsSize, frameSizes, clock⟩

/-- Primitive application preserves control fields, accounting for installation
resetting the frame-size map. -/
theorem doApp_controlFrame {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doApp op args state = .val (value, next)) :
    SameLocalControl {state with stackFrameSizes := if op == .install then .ln else state.stackFrameSizes} next := by
  by_cases install : op = .install
  · subst op
    simp only [doApp] at run
    simp only [beq_self_eq_true, ↓reduceIte]
    simp only [doInstall] at run
    repeat' (split at run <;> try simp_all)
    all_goals obtain ⟨_, rfl⟩ := run
    all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · have check : (op == .install) = false := by simp [install]
    simp only [check, Bool.false_eq_true, ↓reduceIte]
    simp only [doApp] at run
    repeat' (split at run <;> try simp_all)
    all_goals have aux := doAppAux_controlFrame _ _ _ _ _ run
    all_goals have before := doSpace_frame _ _ state _ (by assumption)
    all_goals simpa [SameLocalControl, doStack, doLimSafe, before.1, before.2.1, before.2.2.1,
      before.2.2.2.1, before.2.2.2.2.1, before.2.2.2.2.2] using aux

/-- Cutting the local environment leaves the control and clock fields intact. -/
theorem cutStateOpt_control {C F : Type} (live : Option NumSet) (state next : State C F)
    (run : cutStateOpt live state = some next) :
    next.stack = state.stack ∧ next.handler = state.handler ∧ next.localsSize = state.localsSize ∧
      next.stackFrameSizes = state.stackFrameSizes ∧ next.clock = state.clock := by
  cases live with
  | none => simp [cutStateOpt] at run; subst next; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | some names =>
    cases cut : cutEnv names state.locals with
    | none => simp [cutStateOpt, cutState, cut] at run
    | some env =>
      simp [cutStateOpt, cutState, cut] at run
      subst next
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Successful `makeSpace` changes locals and resource accounting, while
preserving control metadata. -/
theorem evaluate_makeSpace_control {C F : Type} (amount : Nat) (names : NumSet) (state next : State C F)
    (run : evaluate (.makeSpace amount names) state = (none, next)) : SameControl state next := by
  cases cut : cutEnv names state.locals with
  | none => simp [evaluate, cut] at run
  | some env =>
    simp [evaluate, cut] at run
    subst next
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A normally continuing sequence preserves control when each component
does. The first component's clock preservation discharges the clock clamp. -/
theorem evaluate_seq_control {C F : Type} (first second : DataLang.Prog) (state next : State C F)
    (firstFrame : ∀ before after : State C F, evaluate first before = (none, after) → SameControl before after)
    (secondFrame : ∀ before after : State C F, evaluate second before = (none, after) → SameControl before after)
    (run : evaluate (.seq first second) state = (none, next)) : SameControl state next := by
  generalize firstRun : evaluate first state = pair
  obtain ⟨pres, mid⟩ := pair
  cases pres with
  | some result => simp [evaluate, firstRun, fixClock] at run
  | none =>
    have firstControl := firstFrame state mid firstRun
    have clock := firstControl.2.2.2.2
    have bound : mid.clock ≤ state.clock := by rw [clock]
    have clamp : fixClock state ((none : Option (Result (List Value) Value)), mid) = (none, mid) := by
      simp [fixClock, Nat.min_eq_right bound]
    have secondRun : evaluate second mid = (none, next) := by
      rw [evaluate, firstRun, clamp] at run
      exact run
    exact firstControl.trans (secondFrame mid next secondRun)

/-- Invert a normally continuing sequence when the first program preserves
its clock; the second program then starts from the actual intermediate state. -/
theorem evaluate_seq_inv_control {C F : Type} (first second : DataLang.Prog) (state next : State C F)
    (firstFrame : ∀ before after : State C F, evaluate first before = (none, after) → SameControl before after)
    (run : evaluate (.seq first second) state = (none, next)) :
    ∃ mid, evaluate first state = (none, mid) ∧ evaluate second mid = (none, next) := by
  generalize firstRun : evaluate first state = pair
  obtain ⟨pres, mid⟩ := pair
  cases pres with
  | some result => simp [evaluate, firstRun, fixClock] at run
  | none =>
    have clock := (firstFrame state mid firstRun).2.2.2.2
    have bound : mid.clock ≤ state.clock := by rw [clock]
    have clamp : fixClock state ((none : Option (Result (List Value) Value)), mid) = (none, mid) := by
      simp [fixClock, Nat.min_eq_right bound]
    refine ⟨mid, rfl, ?_⟩
    rw [evaluate, firstRun, clamp] at run
    exact run

/-- Invert a successful assignment using a frame theorem for its primitive.
The returned intermediate states expose the actual read, cut, application and
destination update performed by the evaluator. -/
theorem evaluate_assign_frame {C F : Type} (op : ClosLang.Op) (dest : Nat)
    (names : List Nat) (live : Option NumSet) (state next : State C F)
    (primitiveFrame : ∀ (args : List Value) (before after : State C F) (value : Value),
      doApp op args before = .val (value, after) →
      SameLocalControl before after)
    (run : evaluate (.assign dest op names live) state = (none, next)) :
    ∃ args prepared applied value,
      getVars names state.locals = some args ∧ cutStateOpt live state = some prepared ∧
      doApp op args prepared = .val (value, applied) ∧
      next = setVar dest value (installSfs op applied) ∧ SameLocalControl prepared applied := by
  by_cases flag : (DataLang.opRequiresNames op == live.isNone) = true
  · simp [evaluate, flag] at run
  · cases read : getVars names state.locals with
    | none => simp [evaluate, flag, read] at run
    | some args =>
      cases cut : cutStateOpt live state with
      | none => simp [evaluate, flag, read, cut] at run
      | some prepared =>
        cases app : doApp op args prepared with
        | err error => simp [evaluate, flag, read, cut, app] at run
        | val pair =>
          obtain ⟨value, applied⟩ := pair
          simp [evaluate, flag, read, cut, app] at run
          subst next
          exact ⟨args, prepared, applied, value, rfl, rfl, app, rfl, primitiveFrame args prepared applied value app⟩

/-- A successful assignment updates only its destination in the cut local
environment and preserves the original control fields. -/
theorem evaluate_assign_locals {C F : Type} (op : ClosLang.Op) (dest : Nat)
    (names : List Nat) (live : Option NumSet) (state next : State C F)
    (primitiveFrame : ∀ (args : List Value) (before after : State C F) (value : Value),
      doApp op args before = .val (value, after) → SameLocalControl before after)
    (run : evaluate (.assign dest op names live) state = (none, next)) :
    ∃ prepared value, cutStateOpt live state = some prepared ∧
      next.locals = sptInsert dest value prepared.locals ∧ SameControl state next := by
  obtain ⟨args, prepared, applied, value, read, cut, app, output, frame⟩ :=
    evaluate_assign_frame op dest names live state next primitiveFrame run
  have cutControl := cutStateOpt_control live state prepared cut
  rcases cutControl with ⟨stack1, handler1, size1, sizes1, clock1⟩
  rcases frame with ⟨locals, stack2, handler2, size2, sizes2, clock2⟩
  refine ⟨prepared, value, cut, ?_, ?_⟩
  · rw [output]
    simp [setVar, installSfs, locals]
  · rw [output]
    simp [SameControl, setVar, installSfs, stack2, handler2, size2, sizes2, clock2,
      stack1, handler1, size1, sizes1, clock1]

/-- Integer assignment execution exposes its cut and preserves all other
local/control fields through the primitive dispatcher. -/
theorem evaluate_assign_int_frame {C F : Type} (op : ClosLang.IntOp) (dest : Nat)
    (names : List Nat) (live : Option NumSet) (state next : State C F)
    (run : evaluate (.assign dest (.intOp op) names live) state = (none, next)) :
    ∃ args prepared applied value,
      getVars names state.locals = some args ∧ cutStateOpt live state = some prepared ∧
      doApp (.intOp op) args prepared = .val (value, applied) ∧
      next = setVar dest value (installSfs (.intOp op) applied) ∧ SameLocalControl prepared applied :=
  evaluate_assign_frame (.intOp op) dest names live state next (fun args before after value run => by simpa using doApp_controlFrame (.intOp op) args before after value run) run

/-- Word assignment execution has the same local/control frame. -/
theorem evaluate_assign_word_frame {C F : Type} (op : ClosLang.WordOp) (dest : Nat)
    (names : List Nat) (live : Option NumSet) (state next : State C F)
    (run : evaluate (.assign dest (.wordOp op) names live) state = (none, next)) :
    ∃ args prepared applied value,
      getVars names state.locals = some args ∧ cutStateOpt live state = some prepared ∧
      doApp (.wordOp op) args prepared = .val (value, applied) ∧
      next = setVar dest value (installSfs (.wordOp op) applied) ∧ SameLocalControl prepared applied :=
  evaluate_assign_frame (.wordOp op) dest names live state next (fun args before after value run => by simpa using doApp_controlFrame (.wordOp op) args before after value run) run

/-- A successful word assignment preserves the control stack and metadata. -/
theorem evaluate_assign_word_control {C F : Type} (op : ClosLang.WordOp) (dest : Nat)
    (names : List Nat) (live : Option NumSet) (state next : State C F)
    (run : evaluate (.assign dest (.wordOp op) names live) state = (none, next)) : SameControl state next := by
  obtain ⟨args, prepared, applied, value, read, cut, app, output, frame⟩ :=
    evaluate_assign_word_frame op dest names live state next run
  have cutControl := cutStateOpt_control live state prepared cut
  rcases cutControl with ⟨stack1, handler1, size1, sizes1, clock1⟩
  rcases frame with ⟨_, stack2, handler2, size2, sizes2, clock2⟩
  rw [output]
  simp [SameControl, setVar, installSfs, stack2, handler2, size2, sizes2, clock2,
    stack1, handler1, size1, sizes1, clock1]

end Flapjack.Compiler.Backend.DataSem
