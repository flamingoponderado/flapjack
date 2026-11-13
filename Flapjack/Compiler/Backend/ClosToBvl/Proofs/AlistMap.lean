module

public import Flapjack.FiniteMap.AlistExact
public import Flapjack.FiniteMap.UpdateListExact
public import Flapjack.FiniteMap.EmptyExact
public import Flapjack.FiniteMap.MapKeys

@[expose] public section

/-! Distinct association lists and list-updated HOL finite maps. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack

/-- Distinct keys make first-binding and last-update association maps agree. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "alist_to_fmap_FEMPTY"
  (fmap_as_finite_support_result_observations :=
    [Flapjack.HolFiniteMapExact.alistToFmap, Flapjack.HolFiniteMapExact.holUpdateList,
     Flapjack.HolFiniteMapExact.holEmpty])]
theorem alistToFmap_fempty {α β : Type} (xs : List (α × β)) (distinct : (xs.map Prod.fst).Nodup) :
    HolFiniteMapExact.alistToFmap xs =
      HolFiniteMapExact.holUpdateList HolFiniteMapExact.holEmpty xs := by
  classical
  induction xs with
  | nil => rfl
  | cons entry rest ih =>
    have parts := List.nodup_cons.mp distinct
    apply HolFiniteMapExact.ext_lookup
    intro key
    by_cases same : key = entry.1
    · subst key
      rw [HolFiniteMapExact.lookup_alistToFmap_head]
      change some entry.2 = FUPDATE_LIST_HOL (FUPDATE_HOL FEMPTY entry) rest entry.1
      rw [FUPDATE_LIST_HOL_single_commutes _ entry rest parts.1]
      simp [FUPDATE_HOL]
    · rw [HolFiniteMapExact.lookup_alistToFmap_tail entry rest key same]
      have equalTail := congrArg (fun m : HolFiniteMapExact α β => m.lookup key) (ih parts.2)
      rw [equalTail]
      change FUPDATE_LIST_HOL FEMPTY rest key =
        FUPDATE_LIST_HOL (FUPDATE_HOL FEMPTY entry) rest key
      rw [FUPDATE_LIST_HOL_single_commutes _ entry rest parts.1]
      simp [FUPDATE_HOL, same]
end Flapjack.Compiler.Backend.ClosToBvl
