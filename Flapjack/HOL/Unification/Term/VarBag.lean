module

public import Flapjack.HOL.Unification.Term
public import Flapjack.Misc.Bag

@[expose] public section

/-! Variable multiplicities in first-order unification terms. -/
namespace Flapjack.HOL.Unification

@[hol "HOL/examples/algorithms/unification/triangular/first-order/termScript.sml" "varb_def"]
noncomputable def varb {α : Type} : Term α → Bag Nat
  | .var v => bagInsert v emptyBag
  | .pair a b => bagUnion (varb a) (varb b)
  | .const _ => emptyBag

@[hol "HOL/examples/algorithms/unification/triangular/first-order/termScript.sml" "FINITE_varb"]
theorem finiteVarb {α : Type} (t : Term α) : finiteBag (varb t) := by
  induction t with
  | var v => exact finiteBagInsert _ finiteEmptyBag v
  | pair a b ha hb => exact finiteBagUnion _ ha _ hb
  | const c => exact finiteEmptyBag

end Flapjack.HOL.Unification
