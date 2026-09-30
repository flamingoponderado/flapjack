import Flapjack.Compiler.Backend.WordAlloc.Proofs.StrongLocalsRel

namespace Flapjack.WordAlloc

/-- Flapjack factoring of the final lookup-union argument in HOL
cut_env_lemma (word_allocProofScript.sml:360-377). It has no standalone HOL
original and is not the full cut theorem. Its domain and restricted-relation
premises are proved by cut_envs_lemma inside that theorem, not added to the
HOL theorem's hypotheses. Scoped injection prevents a first-only source key
from being hidden by a renamed second-tree key. -/
theorem strongLocalsRelRestrictedTreeUnion {β : Type}
    (f : Nat → Nat) (a b : Nat → Prop) (x1 x2 y1 y2 : Spt β)
    (hinj : ∀ n m, (a n ∨ b n) → (a m ∨ b m) → f n = f m → n = m)
    (hdom1 : sptDomain x1 = a) (hdom2 : sptDomain x2 = b)
    (htdom2 : sptDomain y2 = (fun key => ∃ source, b source ∧ f source = key))
    (hrel1 : strongLocalsRel f a x1 y1) (hrel2 : strongLocalsRel f b x2 y2) :
    strongLocalsRel f (fun key => a key ∨ b key) (sptUnion x2 x1) (sptUnion y2 y1) := by
  intro n v hn
  have hsource := hn.2
  rw [sptLookup_sptUnion] at hsource
  cases hx2 : sptLookup n x2 with
  | some w =>
    have hw : w = v := by simpa [hx2] using hsource
    subst w
    have hnb : b n := by
      rw [← hdom2]
      exact (sptMem_iff_lookup n x2).mpr ⟨v, hx2⟩
    have htarget := hrel2 n v ⟨hnb, hx2⟩
    rw [sptLookup_sptUnion, htarget]
  | none =>
    have hx1 : sptLookup n x1 = some v := by simpa [hx2] using hsource
    have hna : a n := by
      rw [← hdom1]
      exact (sptMem_iff_lookup n x1).mpr ⟨v, hx1⟩
    have hnotb : ¬ b n := by
      intro hb
      have hmem : sptDomain x2 n := by rwa [hdom2]
      obtain ⟨w, hw⟩ := (sptMem_iff_lookup n x2).mp hmem
      simp [hx2] at hw
    have htargetNone : sptLookup (f n) y2 = none := by
      cases ht : sptLookup (f n) y2 with
      | none => rfl
      | some w =>
        exfalso
        have hmem : sptDomain y2 (f n) :=
          (sptMem_iff_lookup (f n) y2).mpr ⟨w, ht⟩
        rw [htdom2] at hmem
        obtain ⟨source, hb, heq⟩ := hmem
        have hequal := hinj source n (Or.inr hb) hn.1 heq
        subst source
        exact hnotb hb
    rw [sptLookup_sptUnion, htargetNone]
    exact hrel1 n v ⟨hna, hx1⟩

end Flapjack.WordAlloc
