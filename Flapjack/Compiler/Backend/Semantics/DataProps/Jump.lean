module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Control

@[expose] public section

/-! Exception-jump transport for states with the same control stack. -/
namespace Flapjack.Compiler.Backend.DataSem

/-- An exception jump depends on the input stack and handler for its control
fields; all other fields come from the state being jumped. This auxiliary
lemma has no direct HOL counterpart. -/
theorem jumpExc_transport {C F : Type} (source target jumped : State C F)
    (stack : target.stack = source.stack) (handler : target.handler = source.handler)
    (run : jumpExc source = some jumped) :
    jumpExc target = some { target with stack := jumped.stack, handler := jumped.handler, locals := jumped.locals, localsSize := jumped.localsSize } := by
  unfold jumpExc at run ⊢
  rw [stack, handler]
  split at run <;> simp_all
  split at run <;> simp_all
  subst jumped
  simp


/-- Exact HOL `jump_exc_NONE` (`dataPropsScript.sml:1819`): the handler search
reads only the handler index and the control stack, so updates to the locals,
clock, stack maximum, locals size and safety flag preserve its outcome. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "jump_exc_NONE"]
theorem jumpExc_none_frame {C F : Type} (state : State C F) (locals : Spt DataSem.Value)
    (clock : Nat) (mx : Option Nat) (localsSize : Option Nat) (safe : Bool) :
    (jumpExc { state with locals := locals } = none ↔ jumpExc state = none) ∧
    (jumpExc { state with clock := clock } = none ↔ jumpExc state = none) ∧
    (jumpExc { state with stackMax := mx } = none ↔ jumpExc state = none) ∧
    (jumpExc { state with localsSize := localsSize } = none ↔ jumpExc state = none) ∧
    (jumpExc { state with safeForSpace := safe } = none ↔ jumpExc state = none) := by
  have frame {a b : State C F} (handler : a.handler = b.handler) (stack : a.stack = b.stack) :
      (jumpExc a = none ↔ jumpExc b = none) := by
    unfold jumpExc
    rw [handler, stack]
    by_cases h : b.handler < b.stack.length
    · simp only [if_pos h]
      split <;> simp
    · simp [h]
  exact ⟨frame rfl rfl, frame rfl rfl, frame rfl rfl, frame rfl rfl, frame rfl rfl⟩

end Flapjack.Compiler.Backend.DataSem
