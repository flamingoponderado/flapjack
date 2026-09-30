import Flapjack.HolRef
import Flapjack.Misc.LprefixLub

/-!
# pan_globals: `LUB_IMAGE_SUC` (the `semantics_init_call` group)

Counterpart of `cakeml/pancake/proofs/pan_globalsProofScript.sml:2663-2710`
(bead `flapjack-pxn.18.5.2.22.3.2.3`), the LUB helper of `semantics_init_call`.
HOL's `LUB` is the `lprefix_lub` overload of `build_lprefix_lub`
(`lprefix_lubScript.sml:560`), rendered as `HolLList.buildLprefixLub`.  A set
`IMAGE f 𝕌(:num)` is the predicate `fun l => ∃ k, l = f k`, exactly as in the
tagged panSem `semantics_def`.
-/

namespace Flapjack

open HolLList

/-- Exact HOL `LUB_IMAGE_SUC[local]` (`pan_globalsProofScript.sml:2663-2665`):
    `(∀x. LPREFIX (f x) (f (SUC x))) ⇒
     LUB (IMAGE f 𝕌(:num)) = LUB (IMAGE (f o SUC) 𝕌(:num))`.
    HOL's proof: `IMP_build_lprefix_lub_EQ` with both images `lprefix_chain`s
    (by `LPREFIX_TRANS` along the monotone sequence) and both `lprefix_rel`
    directions. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "LUB_IMAGE_SUC"]
theorem lubImageSuc {α : Type} (f : Nat → HolLList α)
    (h : ∀ x, lprefix (f x) (f (Nat.succ x))) :
    buildLprefixLub (fun l => ∃ k, l = f k) =
      buildLprefixLub (fun l => ∃ k, l = (f ∘ Nat.succ) k) := by
  have mono : ∀ i d, lprefix (f i) (f (i + d)) := by
    intro i d
    induction d with
    | zero => exact lprefix_refl _
    | succ d ih => exact lprefix_trans ih (h (i + d))
  have cmp : ∀ i j, lprefix (f i) (f j) ∨ lprefix (f j) (f i) := by
    intro i j
    rcases Nat.le_total i j with hij | hji
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
      exact Or.inl (mono i d)
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hji
      exact Or.inr (mono j d)
  apply IMP_build_lprefix_lub_EQ
  · rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩; exact cmp i j
  · rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩; exact cmp (i + 1) (j + 1)
  · rintro _ ⟨k, rfl⟩; exact ⟨f (k + 1), ⟨k, rfl⟩, h k⟩
  · rintro _ ⟨k, rfl⟩; exact ⟨f (k + 1), ⟨k + 1, rfl⟩, lprefix_refl _⟩

end Flapjack
