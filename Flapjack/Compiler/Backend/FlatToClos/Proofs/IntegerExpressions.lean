module

public import Flapjack.Compiler.Backend.FlatToClos.Proofs.IntegerOperations
public import Flapjack.Compiler.Backend.FlatToClos.Proofs.EvaluateCases
public import Flapjack.Compiler.Backend.FlatToClos.Proofs.ValueRelation
public import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyFlat
public import Flapjack.Compiler.Backend.Semantics.FlatSem.Primitives
public import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyBasic

@[expose] public section

/-! Integer-expression cases for flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL

/-- Integer comparison results agree with the closure integer predicates. -/
theorem intCmp_predicates (left right : Int) :
    intCmp .lt left right = decide (left < right) ∧
    intCmp .leq left right = decide (left ≤ right) ∧
    intCmp .gt left right = decide (left > right) ∧
    intCmp .geq left right = decide (left ≥ right) := by
  cases order : compare left right with
  | lt =>
    have lt : left < right := Int.compare_eq_lt.mp order
    simp only [intCmp, order]
    change true = decide (left < right) ∧ true = decide (left ≤ right) ∧
      false = decide (left > right) ∧ false = decide (left ≥ right)
    simp [lt, show left ≤ right by omega, show ¬right < left by omega, show ¬right ≤ left by omega]
  | eq =>
    have equal : left = right := Int.compare_eq_eq.mp order
    subst right
    simp only [intCmp, order]
    change false = decide (left < left) ∧ true = decide (left ≤ left) ∧
      false = decide (left > left) ∧ true = decide (left ≥ left)
    simp
  | gt =>
    have gt : right < left := Int.compare_eq_gt.mp order
    simp only [intCmp, order]
    change false = decide (left < right) ∧ false = decide (left ≤ right) ∧
      true = decide (left > right) ∧ true = decide (left ≥ right)
    simp [gt, show right ≤ left by omega, show ¬left < right by omega, show ¬left ≤ right by omega]

end Flapjack.Compiler.Backend.FlatToClos
