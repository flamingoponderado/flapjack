import Flapjack.Compiler.Backend.StackProps.OrderedLabels

/-! Ten fresh original ordered-label observations, including nested order,
duplicates and an exception continuation ignored by a tail Call. -/
namespace Flapjack.Test.StackPropsOrderedLabelsParity
open Flapjack
open Flapjack.Compiler.Backend.StackLang Flapjack.StackPropsCodeLabels
private def leaf {width : Nat} [NeZero width] (a b : Nat) : HolProg width :=
  .call (some (.skip,0,a,b)) (.inl 0) none
private theorem ordered_skip : extractLabels (.skip : HolProg 64) = [] := by decide +kernel
private theorem ordered_ignore_handler :
    extractLabels (.call none (.inl 7) (some (leaf 3 4,1,2)) : HolProg 64) = [] := by decide +kernel
private theorem ordered_return :
    extractLabels (.call (some (.skip,9,1,2)) (.inr 7) none : HolProg 64) = [(1,2)] := by decide +kernel
private theorem ordered_both :
    extractLabels (.call (some (.skip,9,1,2)) (.inl 7) (some (.skip,3,4)) : HolProg 64) =
      [(1,2),(3,4)] := by decide +kernel
private theorem ordered_nested :
    extractLabels (.call (some (leaf 5 6,9,1,2)) (.inl 7) (some (leaf 7 8,3,4)) : HolProg 64) =
      [(1,2),(3,4),(5,6),(7,8)] := by decide +kernel
private theorem ordered_duplicate :
    extractLabels (.call (some (leaf 1 2,9,1,2)) (.inl 7) (some (.skip,1,2)) : HolProg 1) =
      [(1,2),(1,2),(1,2)] := by decide +kernel
private theorem ordered_sequence :
    extractLabels (.seq (leaf 3 4) (leaf 1 2) : HolProg 80) = [(3,4),(1,2)] := by decide +kernel
private theorem ordered_loop : extractLabels (.loop (leaf 1 2) : HolProg 64) = [(1,2)] := by decide +kernel
private theorem ordered_if :
    extractLabels (.ite .equal 0 (.reg 1) (leaf 3 4) (leaf 1 2) : HolProg 64) =
      [(3,4),(1,2)] := by decide +kernel
private theorem ordered_leaf_labels :
    extractLabels (.seq (.locValue 0 1 2) (.jumpLower 0 1 7) : HolProg 64) = [] := by decide +kernel

/-- Flapjack regression for generic-width unfolding, with no separate HOL theorem. -/
example {width : Nat} [NeZero width] (body : HolProg width) :
    extractLabels (.loop body) = extractLabels body := by simp [extractLabels]

private def code80 : Flapjack.Spt (HolProg 80) := Flapjack.sptFromAList [(7,leaf 1 2)]
private def code1 : Flapjack.Spt (HolProg 1) := Flapjack.sptFromAList [(7,leaf 1 2)]

/-- Flapjack direct application of the original theorem at independent widths. -/
example : ∀ label, Flapjack.StackSem.getLabelsExact (leaf 1 2 : HolProg 80) label →
    Flapjack.StackSem.locCheckExact code80 label :=
  findCodeImpGetLabels (.inl 7 : Sum Nat Bool)
    (Flapjack.HolFiniteMapExact.empty : Flapjack.HolFiniteMapExact Bool (Flapjack.WordLocW 1))
    code80 (leaf 1 2) (by simp [StackSemControl.findCode, code80, sptLookup_sptFromAList, sptAListLookup])

/-- Flapjack indirect application with list keys and reversed independent widths. -/
example : ∀ label, Flapjack.StackSem.getLabelsExact (leaf 1 2 : HolProg 1) label →
    Flapjack.StackSem.locCheckExact code1 label :=
  findCodeImpGetLabels (.inr [1,2])
    (Flapjack.HolFiniteMapExact.empty.updateEq ([1,2],(.loc 7 0 : Flapjack.WordLocW 80)))
    code1 (leaf 1 2) (by simp [StackSemControl.findCode, code1, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, sptLookup_sptFromAList, sptAListLookup])

def runChecks : IO Bool := do
  IO.println "PASS original StackProps ordered labels (10 kernel observations)"
  pure true
end Flapjack.Test.StackPropsOrderedLabelsParity
