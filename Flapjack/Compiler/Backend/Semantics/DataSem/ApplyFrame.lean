import Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate

/-! Local and control fields preserved by numeric primitive application. -/
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
  · simp only [jumpExc, stack, handler, if_pos h] at available ⊢
    cases frame : before.stack.drop (before.stack.length - (before.handler + 1)) with
    | nil => simp [frame] at available
    | cons head rest => cases head <;> simp_all
  · simp [jumpExc, h] at available

/-- Local/control preservation composes across bookkeeping steps. -/
theorem SameLocalControl.trans {C F : Type} {a b c : State C F}
    (first : SameLocalControl a b) (second : SameLocalControl b c) : SameLocalControl a c := by
  rcases first with ⟨a1, a2, a3, a4, a5, a6⟩
  rcases second with ⟨b1, b2, b3, b4, b5, b6⟩
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6⟩

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

/-- A successful integer auxiliary operation leaves local and control fields
unchanged. This is Flapjack infrastructure for compiler-pass simulation. -/
theorem doAppAux_int_frame {C F : Type} (op : ClosLang.IntOp) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.intOp op) args state = .val (value, next)) : SameLocalControl state next := by
  cases intResult : doIntApp op args with
  | none => simp [doAppAux, applyNonFfi, intResult] at run
  | some result =>
    simp [doAppAux, applyNonFfi, intResult] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A successful word auxiliary operation leaves local and control fields
unchanged, including for floating-point word operations. -/
theorem doAppAux_word_frame {C F : Type} (op : ClosLang.WordOp) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.wordOp op) args state = .val (value, next)) : SameLocalControl state next := by
  cases wordResult : doWordApp op args with
  | none => simp [doAppAux, applyNonFfi, wordResult] at run
  | some result =>
    simp [doAppAux, applyNonFfi, wordResult] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem intAccounting_frame {C F : Type} (op : ClosLang.IntOp) (args : List Value)
    (state accounted next : State C F) (value : Value)
    (space : doSpace (.intOp op) args state = some accounted)
    (aux : doAppAux (.intOp op) args
      (doStack (.intOp op) args (doLimSafe accounted (.intOp op) args)) = .val (value, next)) :
    SameLocalControl state next := by
  have first := doSpace_frame (.intOp op) args state accounted space
  have second := doAppAux_int_frame op args _ next value aux
  have second' : SameLocalControl accounted next := by
    simpa [SameLocalControl, doStack, doLimSafe] using second
  exact first.trans second'

/-- A successful full integer dispatcher preserves local and control fields,
including the explicit space and stack accounting. -/
theorem doApp_int_frame {C F : Type} (op : ClosLang.IntOp) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doApp (.intOp op) args state = .val (value, next)) : SameLocalControl state next := by
  cases op <;> simp only [doApp] at run
  all_goals try simp at run
  all_goals split at run
  all_goals try simp at run
  all_goals rename_i accounted space
  all_goals exact intAccounting_frame _ args state accounted next value space run

private theorem wordAccounting_frame {C F : Type} (op : ClosLang.WordOp) (args : List Value)
    (state accounted next : State C F) (value : Value)
    (space : doSpace (.wordOp op) args state = some accounted)
    (aux : doAppAux (.wordOp op) args
      (doStack (.wordOp op) args (doLimSafe accounted (.wordOp op) args)) = .val (value, next)) :
    SameLocalControl state next := by
  have first := doSpace_frame (.wordOp op) args state accounted space
  have second := doAppAux_word_frame op args _ next value aux
  have second' : SameLocalControl accounted next := by
    simpa [SameLocalControl, doStack, doLimSafe] using second
  exact first.trans second'

/-- A successful full word dispatcher preserves local and control fields. -/
theorem doApp_word_frame {C F : Type} (op : ClosLang.WordOp) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doApp (.wordOp op) args state = .val (value, next)) : SameLocalControl state next := by
  simp only [doApp] at run
  cases space : doSpace (.wordOp op) args state with
  | none => simp [space] at run
  | some accounted =>
    simp only [space] at run
    exact wordAccounting_frame op args state accounted next value space run

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
  evaluate_assign_frame (.intOp op) dest names live state next (doApp_int_frame op) run

/-- Word assignment execution has the same local/control frame. -/
theorem evaluate_assign_word_frame {C F : Type} (op : ClosLang.WordOp) (dest : Nat)
    (names : List Nat) (live : Option NumSet) (state next : State C F)
    (run : evaluate (.assign dest (.wordOp op) names live) state = (none, next)) :
    ∃ args prepared applied value,
      getVars names state.locals = some args ∧ cutStateOpt live state = some prepared ∧
      doApp (.wordOp op) args prepared = .val (value, applied) ∧
      next = setVar dest value (installSfs (.wordOp op) applied) ∧ SameLocalControl prepared applied :=
  evaluate_assign_frame (.wordOp op) dest names live state next (doApp_word_frame op) run

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
