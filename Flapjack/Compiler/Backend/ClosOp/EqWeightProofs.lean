module

public import Flapjack.Compiler.Backend.ClosOp.EqBudget
public import Flapjack.Compiler.Backend.ClosOp.SourceHelpers

@[expose] public section

/-! Structural measure facts for the equality decomposition. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang

theorem eqNodeWeight_of_cons (x : Exp) (tag : Nat) (xs : List Exp)
    (h : cons x = some (tag, xs)) : eqNodeWeight x = 1 + eqNodesWeight xs := by
  cases x <;> simp [cons, destOp] at h
  case op t op args =>
    cases op <;> try simp [destCons] at h
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
      case cons tag => simp [cons, destOp, destCons] at h

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

end Flapjack.Compiler.Backend.ClosOp
