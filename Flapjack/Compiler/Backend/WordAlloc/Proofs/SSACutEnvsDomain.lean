import Flapjack.Compiler.Backend.Semantics.WordSem.Env

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

end Flapjack.Compiler.Backend.WordAlloc
