import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocals
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMap
import Flapjack.Misc.SptreeLookup

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Full generic original left-deletion relation: source deletion can only
remove an obligation. Arbitrary native Spt trees/payloads are retained. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_locals_rel_delete_left"]
theorem ssaLocalsRelDeleteLeft {α : Type} (next : Nat) (ssa : Spt Nat)
    (source target : Spt α) (name : Nat)
    (related : ssaLocalsRel next ssa source target) :
    ssaLocalsRel next ssa (sptDelete name source) target := by
  refine ⟨related.1, ?_⟩
  intro key value lookup
  rw [sptLookup_sptDelete] at lookup
  by_cases same : key = name
  · simp [same] at lookup
  · rw [if_neg same] at lookup
    exact related.2 key value lookup

/-- Full generic original physical target deletion relation. The original
SSA-map predicate excludes physical registers from its image. No extra domain,
well-formedness, or source/target success premise is assumed. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_locals_rel_delete_right"]
theorem ssaLocalsRelDeleteRight {α : Type} (next : Nat) (ssa : Spt Nat)
    (source target : Spt α) (name : Nat)
    (h : ssaMapOK next ssa ∧ ssaLocalsRel next ssa source target ∧ isPhyVar name) :
    ssaLocalsRel next ssa source (sptDelete name target) := by
  rcases h with ⟨valid, related, physical⟩
  refine ⟨?_, ?_⟩
  · intro key register lookup
    have different : register ≠ name := by
      intro equal
      subst register
      exact (valid key name lookup).1 physical
    obtain ⟨value, read⟩ := (sptMem_iff_lookup register target).mp (related.1 key register lookup)
    apply (sptMem_iff_lookup register (sptDelete name target)).mpr
    exact ⟨value, by rw [sptLookup_sptDelete, if_neg different]; exact read⟩
  · intro key value lookup
    obtain ⟨domain, read, bound⟩ := related.2 key value lookup
    obtain ⟨register, mapped⟩ := (sptMem_iff_lookup key ssa).mp domain
    have different : register ≠ name := by
      intro equal
      subst register
      exact (valid key name mapped).1 physical
    refine ⟨domain, ?_, bound⟩
    simpa only [mapped, Option.getD_some, sptLookup_sptDelete, if_neg different] using read

end Flapjack.Compiler.Backend.WordAlloc
