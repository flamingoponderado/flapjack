module

public import Flapjack.Compiler.Backend.Semantics.WordSem.Env

@[expose] public section

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Full generic original successful-cut input-domain theorem. Cutsets retain
their two Unit-payload native trees and locals their arbitrary payload. Only
the original successful producer equation is assumed; both input-domain
inclusions are derived from actual cut_names guards. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "cut_envs_domain_SUBSET"]
theorem cutEnvsDomainSubset {α : Type} (first second : Spt Unit)
    (locals : Spt α) (output : Spt α × Spt α)
    (cut : wordSemCutEnvs (first,second) locals = some output) :
    (∀ key, sptDomain first key → sptDomain locals key) ∧
    (∀ key, sptDomain second key → sptDomain locals key) := by
  classical
  by_cases firstSubset : LoopSemStateFiniteExact.sptSubsetLive first locals
  · by_cases secondSubset : LoopSemStateFiniteExact.sptSubsetLive second locals
    · exact ⟨firstSubset,secondSubset⟩
    · simp [wordSemCutEnvs,wordSemCutNames,firstSubset,secondSubset] at cut
  · simp [wordSemCutEnvs,wordSemCutNames,firstSubset] at cut

/-- Exact HOL `ssa_cut_inter_lemma` (`word_allocProofScript.sml:7657-7664`):
when the intersection of the reconciled domain with the union domain equals the
union of the two input domains, membership in the union transfers to the
reconciled map. HOL set intersection/union are the predicate `∧`/`∨`. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cut_inter_lemma"]
theorem ssaCutInterLemma {α β : Type} (ssa' : Spt α) (x1 x2 : Spt β) (xx : Nat)
    (h1 : (fun k => sptDomain ssa' k ∧ sptDomain (sptUnion x1 x2) k) =
      (fun k => sptDomain x1 k ∨ sptDomain x2 k))
    (h2 : sptDomain (sptUnion x1 x2) xx) :
    sptDomain ssa' xx := by
  have hx : sptDomain x1 xx ∨ sptDomain x2 xx := by
    simpa [sptDomain_sptUnion] using h2
  have hh := congrFun h1 xx
  simp only [sptDomain_sptUnion] at hh
  simpa [hx] using hh

end Flapjack.Compiler.Backend.WordAlloc
