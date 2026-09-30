import Flapjack.Compiler.Backend.WordAlloc.Proofs.StrongLocalsRel
import Flapjack.Compiler.Backend.WordAlloc.Proofs.KeyMaps
import Flapjack.Compiler.Backend.Semantics.WordSem.Env

namespace Flapjack.WordAlloc

/-- Flapjack factoring of the domain-intersection absorption argument used by
HOL cut_names_lemma. It has no separate CakeML original. -/
private theorem interDomainOfSubset {α β : Type} (names : Spt α) (env : Spt β)
    (h : ∀ key, sptDomain names key → sptDomain env key) :
    sptDomain (sptInter env names) = sptDomain names := by
  rw [sptDomain_sptInter]
  funext key
  exact propext ⟨And.right, fun hk => ⟨h key hk, hk⟩⟩

/-- Exact HOL cut_names_lemma: successful source restriction and the
live-scoped local relation produce a successful renamed target restriction,
its full image domain, the restricted relation and the inherited injection.
No successful target cut or global injectivity is assumed. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "cut_names_lemma"]
theorem cutNamesLemma {α β : Type}
    (names : Spt α) (sloc tloc x : Spt β) (f : Nat → Nat)
    (h : (∀ a b, sptDomain names a → sptDomain names b → f a = f b → a = b) ∧
      wordSemCutNames names sloc = some x ∧ strongLocalsRel f (sptDomain names) sloc tloc) :
    ∃ y, wordSemCutNames (applyNummapKey f names) tloc = some y ∧
      sptDomain y = (fun key => ∃ source, sptDomain x source ∧ f source = key) ∧
      strongLocalsRel f (sptDomain names) x y ∧
      (∀ a b, sptDomain x a → sptDomain x b → f a = f b → a = b) ∧
      sptDomain x = sptDomain names := by
  rcases h with ⟨hinj, hcut, hrel⟩
  have hsub : LoopSemStateFiniteExact.sptSubsetLive names sloc := by
    by_cases hn : LoopSemStateFiniteExact.sptSubsetLive names sloc
    · exact hn
    · simp [wordSemCutNames, hn] at hcut
  have hx : sptInter sloc names = x := by
    simpa [wordSemCutNames, hsub] using hcut
  subst x
  have hdom := interDomainOfSubset names sloc hsub
  have htSub : LoopSemStateFiniteExact.sptSubsetLive (applyNummapKey f names) tloc := by
    intro key hk
    change sptDomain (applyNummapKey f names) key at hk
    rw [applyNummapKeyDomain] at hk
    obtain ⟨source, hsource, heq⟩ := hk
    obtain ⟨value, hv⟩ := (sptMem_iff_lookup source sloc).mp (hsub source hsource)
    subst key
    exact (sptMem_iff_lookup (f source) tloc).mpr ⟨value, hrel source value ⟨hsource, hv⟩⟩
  refine ⟨sptInter tloc (applyNummapKey f names), ?_, ?_, ?_, ?_, hdom⟩
  · simp [wordSemCutNames, htSub]
  · rw [interDomainOfSubset _ _ htSub, applyNummapKeyDomain, hdom]
  · intro key value hk
    obtain ⟨nv, hn⟩ := (sptMem_iff_lookup key names).mp hk.1
    have hsrc : sptLookup key sloc = some value := by
      have hlookup := hk.2
      rw [sptLookup_sptInterCases, hn] at hlookup
      cases hs : sptLookup key sloc with
      | none => simp [hs] at hlookup
      | some w => simpa [hs] using hlookup
    have htarget := hrel key value ⟨hk.1, hsrc⟩
    have hname : sptDomain (applyNummapKey f names) (f key) := by
      rw [applyNummapKeyDomain]
      exact ⟨key, hk.1, rfl⟩
    obtain ⟨tv, htn⟩ := (sptMem_iff_lookup (f key) (applyNummapKey f names)).mp hname
    rw [sptLookup_sptInterCases, htarget, htn]
  · simpa [hdom] using hinj

end Flapjack.WordAlloc
