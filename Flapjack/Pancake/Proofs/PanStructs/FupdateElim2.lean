import Flapjack.HolRef
import Flapjack.Pancake.Semantics.CrepSem.HOLState
namespace Flapjack.Pancake.Proofs.PanStructs.FupdateElim2
open Flapjack
/-- Full original local finite-map update neutrality. Classical equality is
HOL equality; there is no additional public decision or comparison premise. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "fupdate_elim2"
  (fmap_as_finite_support_relation := [fm])]
theorem fupdateElim2 {α β : Type} (fm : HolFiniteMapExact α β) (x : α) (y : β)
    (h : fm.lookup x = some y) :
    @HolFiniteMapExact.updateEq α β (Classical.typeDecidableEq α) fm (x, y) = fm := by
  classical
  cases fm with
  | mk lookup finiteSupport =>
    simp only [HolFiniteMapExact.updateEq]
    congr 1
    funext key
    simp only [FUPDATE_HOL]
    by_cases hk : key = x
    · subst key
      simpa using h.symm
    · simp [hk]

end Flapjack.Pancake.Proofs.PanStructs.FupdateElim2
