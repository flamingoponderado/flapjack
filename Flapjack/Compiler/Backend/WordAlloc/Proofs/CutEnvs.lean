import Flapjack.Compiler.Backend.WordAlloc.Proofs.CutNames

namespace Flapjack.WordAlloc

/-- Exact paired restriction simulation from HOL cut_envs_lemma. Successful
source restriction and the two scoped local relations establish target success
and all image-domain, restricted-relation and inherited-injection conclusions.
The environment payload remains generic; no target restriction is assumed. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "cut_envs_lemma"]
theorem cutEnvsLemma {β : Type}
    (n1 n2 : NumSet) (sloc tloc x1 x2 : Spt β) (f : Nat → Nat)
    (h : (∀ a b, sptDomain n1 a → sptDomain n1 b → f a = f b → a = b) ∧
      (∀ a b, sptDomain n2 a → sptDomain n2 b → f a = f b → a = b) ∧
      wordSemCutEnvs (n1, n2) sloc = some (x1, x2) ∧
      strongLocalsRel f (sptDomain n1) sloc tloc ∧
      strongLocalsRel f (sptDomain n2) sloc tloc) :
    ∃ y1 y2, wordSemCutEnvs (applyNummapsKey f (n1, n2)) tloc = some (y1, y2) ∧
      sptDomain y1 = (fun key => ∃ source, sptDomain n1 source ∧ f source = key) ∧
      sptDomain y2 = (fun key => ∃ source, sptDomain n2 source ∧ f source = key) ∧
      strongLocalsRel f (sptDomain n1) x1 y1 ∧
      strongLocalsRel f (sptDomain n2) x2 y2 ∧
      (∀ a b, sptDomain x1 a → sptDomain x1 b → f a = f b → a = b) ∧
      (∀ a b, sptDomain x2 a → sptDomain x2 b → f a = f b → a = b) ∧
      sptDomain x1 = sptDomain n1 ∧ sptDomain x2 = sptDomain n2 := by
  rcases h with ⟨hinj1, hinj2, hcut, hrel1, hrel2⟩
  have hcuts : wordSemCutNames n1 sloc = some x1 ∧
      wordSemCutNames n2 sloc = some x2 := by
    cases hc1 : wordSemCutNames n1 sloc with
    | none => simp [wordSemCutEnvs, hc1] at hcut
    | some v1 =>
      cases hc2 : wordSemCutNames n2 sloc with
      | none => simp [wordSemCutEnvs, hc1, hc2] at hcut
      | some v2 =>
        have heq : v1 = x1 ∧ v2 = x2 := by
          simpa [wordSemCutEnvs, hc1, hc2] using hcut
        rcases heq with ⟨rfl, rfl⟩
        exact ⟨rfl, rfl⟩
  obtain ⟨y1, hy1, hdom1, hrestricted1, hinherited1, hx1⟩ :=
    cutNamesLemma n1 sloc tloc x1 f ⟨hinj1, hcuts.1, hrel1⟩
  obtain ⟨y2, hy2, hdom2, hrestricted2, hinherited2, hx2⟩ :=
    cutNamesLemma n2 sloc tloc x2 f ⟨hinj2, hcuts.2, hrel2⟩
  refine ⟨y1, y2, ?_, ?_, ?_, hrestricted1, hrestricted2,
    hinherited1, hinherited2, hx1, hx2⟩
  · simp [wordSemCutEnvs, applyNummapsKey, hy1, hy2]
  · simpa [hx1] using hdom1
  · simpa [hx2] using hdom2

end Flapjack.WordAlloc
