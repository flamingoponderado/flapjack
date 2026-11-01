import Flapjack.Compiler.Backend.Semantics.DataSem.Control

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

end Flapjack.Compiler.Backend.DataSem
