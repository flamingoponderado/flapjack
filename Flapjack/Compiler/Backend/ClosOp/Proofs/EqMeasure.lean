import Flapjack.Compiler.Backend.ClosOp
import Flapjack.Compiler.Backend.ClosOp.EqBudget

/-! A structural measure for equality decomposition. This is Flapjack
infrastructure for fuel sufficiency, not a HOL theorem port. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang

theorem eqNodeWeight_of_cons (x : Exp) (tag : Nat) (xs : List Exp)
    (h : cons x = some (tag, xs)) : eqNodeWeight x = 1 + eqNodesWeight xs := by
  cases x <;> simp [cons] at h
  case op t op args =>
    cases op <;> try simp at h
    case blockOp op =>
      cases op <;> try simp at h
      case cons tag' =>
        rcases h with ⟨rfl, rfl⟩
        simp [eqNodeWeight]

theorem eqNodeWeight_of_not_cons (x : Exp) (h : cons x = none) : eqNodeWeight x = 0 := by
  cases x <;> try simp [eqNodeWeight]
  case op t op args =>
    cases op <;> try simp [eqNodeWeight]
    case blockOp op =>
      cases op <;> try simp [eqNodeWeight]
      case cons tag => simp [cons] at h

theorem eqNodesWeight_append (xs ys : List Exp) :
    eqNodesWeight (xs ++ ys) = eqNodesWeight xs + eqNodesWeight ys := by
  induction xs with
  | nil => simp [eqNodesWeight]
  | cons x xs ih => simp [eqNodesWeight, ih]; omega

theorem eqNodesWeight_reverse (xs : List Exp) :
    eqNodesWeight xs.reverse = eqNodesWeight xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [eqNodesWeight_append, eqNodesWeight, ih]; omega

theorem eqPairsWeight_zip_le (xs ys : List Exp) :
    eqPairsWeight (xs.zip ys) ≤ 2 * eqNodesWeight xs + 2 * eqNodesWeight ys := by
  induction xs generalizing ys with
  | nil => simp [eqPairsWeight, eqNodesWeight]
  | cons x xs ih =>
    cases ys with
    | nil => simp [eqPairsWeight, eqNodesWeight]
    | cons y ys =>
      have h := ih ys
      simp only [List.zip_cons_cons, eqPairsWeight, eqPairWeight,
        eqNodesWeight]
      split <;> omega

theorem eqPairsWeight_fields_le (xs : List Exp) (y : Exp) (is : List Nat) :
    eqPairsWeight ((xs.zip is).map fun p =>
      (p.1, Exp.op .none (.blockOp (.elemAt p.2)) [y])) ≤ 2 * eqNodesWeight xs := by
  induction xs generalizing is with
  | nil => simp [eqPairsWeight, eqNodesWeight]
  | cons x xs ih =>
    cases is with
    | nil => simp [eqPairsWeight, eqNodesWeight]
    | cons i is =>
      have h := ih is
      simp only [List.zip_cons_cons, List.map_cons, eqPairsWeight, eqPairWeight,
        eqNodeWeight, Nat.not_lt_zero, ↓reduceIte, eqNodesWeight]
      omega

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
  cases h : eqListFuel fuel pairs with
  | some result => exact ⟨result, by simp [eqListBounded, h]⟩
  | none =>
    have bound : eqPairsWeight pairs < max fuel (eqPairsWeight pairs + 1) := by omega
    obtain ⟨result, done⟩ := eqListFuel_succeeds (max fuel (eqPairsWeight pairs + 1)) pairs bound
    exact ⟨result, by simp [eqListBounded, h, done]⟩

/-- Retrying preserves every previously successful equality decomposition. -/
theorem eqListBounded_eq_of_success (fuel : Nat) (pairs : List (Exp × Exp))
    (result : List Exp) (h : eqListFuel fuel pairs = some result) :
    eqListBounded fuel pairs = some result := by
  simp [eqListBounded, h]

end Flapjack.Compiler.Backend.ClosOp
