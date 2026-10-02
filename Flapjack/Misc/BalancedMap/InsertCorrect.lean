import Flapjack.Misc.BalancedMap.InsertCorrect.Tip
import Flapjack.Misc.BalancedMap.InsertCorrect.Equal
import Flapjack.Misc.BalancedMap.InsertCorrect.Less
import Flapjack.Misc.BalancedMap.InsertCorrect.Greater
namespace Flapjack.Misc.BalancedMap
open FiniteMap.Comparison
/-- Full original insertion correctness, retaining arbitrary comparator,
key/payload/tree carriers and both original conclusions. Registration awaits
coordinator acceptance. Original statement and complete closed replay were
compared at HOL lines 1525–1578; the named canonical producer qualifier
records only the finite-map representation translation. -/
@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "insert_thm"
  (fmap_as_finite_support_result_observations := [Flapjack.Misc.BalancedMap.toFmap])]
theorem insertThm {κ ν : Type} (cmp : κ → κ → Ordering) (key : κ) (value : ν)
    (tree : Map κ ν) (h : goodCmp cmp ∧ invariant cmp tree) :
    invariant cmp (insert cmp key value tree) ∧
      Flapjack.Misc.BalancedMap.toFmap cmp (insert cmp key value tree) =
        (Flapjack.Misc.BalancedMap.toFmap cmp tree).updateEq (keySet cmp key, value) := by
  classical
  obtain ⟨hgood, hinv⟩ := h
  induction tree with
  | tip => exact insertCorrectTip cmp key value
  | bin n root oldValue left right ihleft ihright =>
    have hil : invariant cmp left := hinv.2.2.2.2.1
    have hir : invariant cmp right := hinv.2.2.2.2.2
    cases heq : cmp key root with
    | lt => exact insertCorrectLess cmp key root value oldValue n left right hgood hinv heq (ihleft hil)
    | eq => exact insertCorrectEqual cmp key root value oldValue n left right hgood hinv heq
    | gt => exact insertCorrectGreater cmp key root value oldValue n left right hgood hinv heq (ihright hir)
end Flapjack.Misc.BalancedMap
