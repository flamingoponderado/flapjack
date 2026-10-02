import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocals
import Flapjack.Compiler.Backend.WordAlloc.SSAHelpers

namespace Flapjack.Compiler.Backend.WordAlloc

/-- HOL's generic locals relation after forced renaming. The three premises are
unchanged: the original locals relation, matching lookups for every pair, and
membership of every target register in the target domain. Lists and arbitrary
native `Spt` trees retain their original carriers; no distinctness or tree
well-formedness premise is added. The guarded selector in `ssaLocalsRel` is
justified by its selector-independence theorem. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_locals_rel_force_rename"]
theorem ssaLocalsRelForceRename {α : Type} (next : Nat) (ssa : Spt Nat)
    (source target : Spt α) (pairs : List (Nat × Nat))
    (h : ssaLocalsRel next ssa source target ∧
      (∀ pair ∈ pairs, sptLookup pair.1 source = sptLookup pair.2 target) ∧
      (∀ register ∈ pairs.map Prod.snd, sptDomain target register)) :
    ssaLocalsRel next (forceRename pairs ssa) source target := by
  induction pairs generalizing ssa with
  | nil => exact h.1
  | cons pair pairs ih =>
    rcases pair with ⟨name, register⟩
    rcases h with ⟨relation, agree, domain⟩
    have pairRead := agree (name, register) (List.mem_cons_self ..)
    have registerDomain : sptMem register target :=
      domain register (by simp)
    have updated : ssaLocalsRel next (sptInsert name register ssa) source target := by
      rcases relation with ⟨mapped, reads⟩
      constructor
      · intro key value lookup
        by_cases same : key = name
        · subst key
          rw [sptLookup_sptInsert_same] at lookup
          cases lookup
          exact registerDomain
        · rw [sptLookup_sptInsert_ne name key register ssa same] at lookup
          exact mapped key value lookup
      · intro key value lookup
        rcases reads key value lookup with ⟨inDomain, targetRead, bound⟩
        refine ⟨(sptMem_sptInsert key name register ssa).mpr (Or.inr inDomain), ?_, bound⟩
        by_cases same : key = name
        · subst key
          simpa only [sptLookup_sptInsert_same, Option.getD_some] using
            pairRead.symm.trans lookup
        · simpa only [sptLookup_sptInsert_ne name key register ssa same] using targetRead
    apply ih
    exact ⟨updated,
      fun pair member => agree pair (List.mem_cons_of_mem _ member),
      fun value member => domain value (by simp only [List.map_cons, List.mem_cons]; exact Or.inr member)⟩

end Flapjack.Compiler.Backend.WordAlloc
