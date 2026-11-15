module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.Apply

@[expose] public section

namespace Flapjack.Compiler.Backend.ClosSem

/-- The primitive dispatcher never raises a language exception. This
Flapjack-specific fact is used by simulations of the source dispatcher. -/
theorem doApp_not_raise {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : State C F) (value : Value) : doApp op args state ≠ .err (.raise value) := by
  unfold doApp
  repeat' split
  all_goals simp_all
  all_goals split <;> simp_all

end Flapjack.Compiler.Backend.ClosSem
