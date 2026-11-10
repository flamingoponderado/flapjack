module

public import Flapjack.Compiler.Backend.FlatToClos.Proofs.IntegerExpressions

@[expose] public section

/-! Byte and character ordering in flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL

/-- Integer comparison of natural numbers agrees with natural comparison. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "imp_cmp_eq_num_cmp"]
theorem numCmp_intCmp (a b : Nat) (op : Opb) :
    intCmp op (a : Int) (b : Int) = numCmp op a b := by
  have same : compare a b = compare (a : Int) (b : Int) := by
    cases h : compare a b with
    | lt =>
      symm
      apply Int.compare_eq_lt.mpr
      exact_mod_cast Nat.compare_eq_lt.mp h
    | eq =>
      symm
      apply Int.compare_eq_eq.mpr
      exact_mod_cast Nat.compare_eq_eq.mp h
    | gt =>
      symm
      apply Int.compare_eq_gt.mpr
      exact_mod_cast Nat.compare_eq_gt.mp h
  symm
  simp only [numCmp, intCmp, same]

end Flapjack.Compiler.Backend.FlatToClos
