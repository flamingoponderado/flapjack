module

public import Flapjack.HOL.Unification.Term
public import Flapjack.Misc.Bag
import Lean.Elab.Tactic.Omega

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

@[hol "HOL/examples/algorithms/unification/triangular/first-order/termScript.sml" "IN_varb_vars"]
theorem inVarbVars {α : Type} (e : Nat) (t : Term α) : bagIn e (varb t) ↔ vars t e := by
  classical
  induction t with
  | var v =>
    by_cases h : e = v <;> simp [varb, bagIn, bagInn, bagInsert, emptyBag, vars, h]
  | const c => simp [varb, bagIn, bagInn, emptyBag, vars]
  | pair a b ihA ihB =>
    change 1 ≤ varb a e + varb b e ↔ vars a e ∨ vars b e
    rw [← ihA, ← ihB]
    change 1 ≤ varb a e + varb b e ↔ 1 ≤ varb a e ∨ 1 ≤ varb b e
    omega

end Flapjack.HOL.Unification
