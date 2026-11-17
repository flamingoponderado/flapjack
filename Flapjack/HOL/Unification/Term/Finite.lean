module

public import Flapjack.HOL.Unification.Term
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

namespace Flapjack.HOL.Unification

@[hol "HOL/examples/algorithms/unification/triangular/first-order/termScript.sml" "FINITE_vars"]
theorem finiteVars {α : Type} (t : Term α) : Set.Finite (vars t) := by
  induction t with
  | var n =>
    change Set.Finite ({n} : Set Nat)
    exact Set.finite_singleton n
  | pair l r hl hr => exact hl.union hr
  | const c => exact Set.finite_empty

end Flapjack.HOL.Unification
