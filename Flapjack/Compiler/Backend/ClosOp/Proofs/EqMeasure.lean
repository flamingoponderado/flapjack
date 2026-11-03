import Flapjack.Compiler.Backend.ClosOp.Proofs.EqTree
import Flapjack.Compiler.Backend.ClosOp.EqBudget

/-! A structural measure for equality decomposition. This is Flapjack
infrastructure for fuel sufficiency, not a HOL theorem port. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang

/-- A constructor measure bounds every recursive equality decomposition,
including the one-sided constructor swap. -/
theorem eqListFuel_succeeds (fuel : Nat) (pairs : List (Exp × Exp))
    (bound : eqPairsWeight pairs < fuel) :
    ∃ result, eqListFuel fuel pairs = some result := by
  induction fuel generalizing pairs with
  | zero => omega
  | succ fuel ih =>
    cases pairs with
    | nil => exact ⟨_, rfl⟩
    | cons p rest =>
      obtain ⟨x, y⟩ := p
      have pairBound : eqPairWeight (x, y) ≤ fuel := by
        simp only [eqPairsWeight] at bound; omega
      have restBound : eqPairsWeight rest < fuel := by
        simp only [eqPairsWeight, eqPairWeight] at bound
        split at bound <;> omega
      obtain ⟨tail, ht⟩ := ih rest restBound
      cases hd : directEq x y with
      | some e => exact ⟨_, by simp [eqListFuel, hd, ht]; rfl⟩
      | none =>
        cases hx : cons x with
        | none =>
          cases hy : cons y with
          | none => exact ⟨_, by simp [eqListFuel, hd, hx, hy, ht]; rfl⟩
          | some p =>
            obtain ⟨tag, ys⟩ := p
            have wx := eqNodeWeight_of_not_cons x hx
            have wy := eqNodeWeight_of_cons y tag ys hy
            have swapBound : eqPairsWeight [(y, x)] < fuel := by
              simp only [eqPairsWeight, eqPairWeight] at *
              have positive : 0 < 1 + eqNodesWeight ys := by omega
              simp [wx, wy, positive] at *
              omega
            obtain ⟨first, hf⟩ := ih [(y, x)] swapBound
            exact ⟨_, by simp [eqListFuel, hd, hx, hy, hf, ht]; rfl⟩
        | some p =>
          obtain ⟨tag, xs⟩ := p
          cases hy : cons y with
          | none =>
            have wx := eqNodeWeight_of_cons x tag xs hx
            have wy := eqNodeWeight_of_not_cons y hy
            have fieldsBound : eqPairsWeight
                ((xs.reverse.zip (List.range xs.length)).map fun p =>
                  (p.1, Exp.op .none (.blockOp (.elemAt p.2)) [y])) < fuel := by
              have h := eqPairsWeight_fields_le xs.reverse y (List.range xs.length)
              rw [eqNodesWeight_reverse] at h
              simp only [eqPairWeight] at pairBound
              simp [wx, wy] at pairBound
              omega
            obtain ⟨first, hf⟩ := ih _ fieldsBound
            exact ⟨_, by simp [eqListFuel, hd, hx, hy, hf, ht]; rfl⟩
          | some p =>
            obtain ⟨tag', ys⟩ := p
            by_cases hne : tag != tag' || xs.length != ys.length
            · exact ⟨_, by simp [eqListFuel, hd, hx, hy, hne, ht]; rfl⟩
            · have wx := eqNodeWeight_of_cons x tag xs hx
              have wy := eqNodeWeight_of_cons y tag' ys hy
              have zipBound : eqPairsWeight (xs.reverse.zip ys.reverse) < fuel := by
                have h := eqPairsWeight_zip_le xs.reverse ys.reverse
                simp only [eqNodesWeight_reverse] at h
                simp only [eqPairWeight] at pairBound
                rw [wx, wy] at pairBound
                split at pairBound <;> omega
              obtain ⟨first, hf⟩ := ih _ zipBound
              exact ⟨_, by simp [eqListFuel, hd, hx, hy, hne, hf, ht]; rfl⟩

/-- Retried equality decomposition cannot exhaust traversal fuel. -/
theorem eqListBounded_succeeds (fuel : Nat) (pairs : List (Exp × Exp)) :
    ∃ result, eqListBounded fuel pairs = some result := by
  exact ⟨_, rfl⟩

/-- Retrying preserves every previously successful equality decomposition. -/
theorem eqListBounded_eq_of_success (fuel : Nat) (pairs : List (Exp × Exp))
    (result : List Exp) (h : eqListFuel fuel pairs = some result) :
    eqListBounded fuel pairs = some result := by
  simp [eqListBounded, eqFuelFlatten fuel pairs result h]

/-- The total source traversal agrees with the former retrying wrapper for
every input. This preservation fact has no separate HOL declaration. -/
theorem eqListBounded_eq_previous (fuel : Nat) (pairs : List (Exp × Exp)) :
    eqListBounded fuel pairs =
      match eqListFuel fuel pairs with
      | some result => some result
      | none => eqListFuel (max fuel (eqPairsWeight pairs + 1)) pairs := by
  cases h : eqListFuel fuel pairs with
  | some result => exact eqListBounded_eq_of_success fuel pairs result h
  | none =>
    have bound : eqPairsWeight pairs < max fuel (eqPairsWeight pairs + 1) := by omega
    obtain ⟨result, done⟩ := eqListFuel_succeeds (max fuel (eqPairsWeight pairs + 1)) pairs bound
    simpa [h, done, eqListBounded] using eqListBounded_eq_of_success _ pairs result done

end Flapjack.Compiler.Backend.ClosOp
