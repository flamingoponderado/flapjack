import Flapjack.HolRef
import Flapjack.Misc.Sptree.ToAList

/-!
# reg_allocProof: mutually inverse sparse maps

Ports of `reg_allocProofScript.sml:783-800`.
-/

namespace Flapjack.RegAlloc

/-- HOL `sp_inverts` (`reg_allocProofScript.sml:783-788`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "sp_inverts_def"]
def spInverts (f g : Spt Nat) : Prop :=
  ∀ m fm, sptLookup m f = some fm → sptLookup fm g = some m

/-- Exact HOL `sp_inverts_insert` (`reg_allocProofScript.sml:790-800`); the free
`f g x y` are quantified first. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "sp_inverts_insert"]
theorem spInvertsInsert :
    ∀ (f g : Spt Nat) (x y : Nat),
      spInverts f g ∧ ¬ sptDomain f x ∧ ¬ sptDomain g y →
      spInverts (sptInsert x y f) (sptInsert y x g) := by
  intro f g x y ⟨hi, hx, hy⟩ m fm hm
  by_cases hmx : m = x
  · subst hmx
    rw [sptLookup_sptInsert_same] at hm
    cases hm
    exact sptLookup_sptInsert_same _ _ _
  · rw [sptLookup_sptInsert_ne x m y f hmx] at hm
    have h1 := hi m fm hm
    have hfy : fm ≠ y := by
      intro e; subst e; apply hy; simp [sptDomain, h1]
    rw [sptLookup_sptInsert_ne y fm x g hfy]
    exact h1

end Flapjack.RegAlloc
