import Flapjack.HolRef
import Flapjack.Misc.Sptree

namespace Flapjack.Compiler.Backend.RegAlloc

open Flapjack (Spt sptLookup sptInsert)

/-- HOL `sp_inverts_def` (reg_allocProofScript.sml:783-788): `g` inverts the
sparse-map `f` on the values of `f`. Both carriers are `num num_map`, rendered
as `Spt Nat`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "sp_inverts_def"]
def spInverts (f g : Spt Nat) : Prop :=
  ∀ m fm, sptLookup m f = some fm → sptLookup fm g = some m

/-- HOL `sp_inverts_insert` (reg_allocProofScript.sml:790-801): inserting a
fresh pair of keys (`x` absent from `f`, `y` absent from `g`) preserves the
inversion. `domain` membership is rendered as `sptLookup _ = none`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "sp_inverts_insert"]
theorem spInvertsInsert (f g : Spt Nat) (x y : Nat) (h : spInverts f g)
    (_hf : sptLookup x f = none) (hg : sptLookup y g = none) :
    spInverts (sptInsert x y f) (sptInsert y x g) := by
  intro m fm hm
  by_cases hmx : m = x
  · rw [hmx] at hm ⊢
    rw [sptLookup_sptInsert_same] at hm
    injection hm with hfm
    rw [← hfm]
    exact sptLookup_sptInsert_same y x g
  · rw [sptLookup_sptInsert_ne x m y f hmx] at hm
    have hfm := h m fm hm
    by_cases hfmy : fm = y
    · rw [hfmy, hg] at hfm
      cases hfm
    · rw [sptLookup_sptInsert_ne y fm x g hfmy]
      exact hfm

end Flapjack.Compiler.Backend.RegAlloc
