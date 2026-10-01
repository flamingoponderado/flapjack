import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocals
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMap

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Full fresh insertion result with the original generic locals payload and
three conjunctive premises. The old mapped-register bound prevents the new
target insertion from overwriting any previous mapped value. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_locals_rel_insert"]
theorem ssaLocalsRelInsert {α : Type} (next : Nat) (ssa : Spt Nat)
    (source target : Spt α) (name : Nat) (value : α) :
    ssaLocalsRel next ssa source target ∧ ssaMapOK next ssa ∧ name < next →
      ssaLocalsRel (next + 4) (sptInsert name next ssa)
        (sptInsert name value source) (sptInsert next value target) := by
  rintro ⟨⟨mapped, matching⟩, valid, nameBound⟩
  refine ⟨?_, ?_⟩
  · intro key register found
    by_cases same : key = name
    · subst key
      rw [sptLookup_sptInsert_same] at found
      cases found
      exact (sptMem_iff_lookup next _).mpr
        ⟨value, sptLookup_sptInsert_same next value target⟩
    · rw [sptLookup_sptInsert_ne name key next ssa same] at found
      have registerBound := (valid key register found).2
      rcases (sptMem_iff_lookup register target).mp (mapped key register found) with
        ⟨oldValue, oldFound⟩
      apply (sptMem_iff_lookup register _).mpr
      refine ⟨oldValue, ?_⟩
      rw [sptLookup_sptInsert_ne next register value target (by omega)]
      exact oldFound
  · intro key oldValue found
    by_cases same : key = name
    · subst key
      rw [sptLookup_sptInsert_same] at found
      cases found
      refine ⟨(sptMem_iff_lookup name _).mpr
        ⟨next, sptLookup_sptInsert_same name next ssa⟩, ?_, ?_⟩
      · simp only [sptLookup_sptInsert_same, Option.getD_some]
      · intro _
        omega
    · rw [sptLookup_sptInsert_ne name key value source same] at found
      rcases matching key oldValue found with ⟨domain, oldLookup, oldBound⟩
      rcases (sptMem_iff_lookup key ssa).mp domain with ⟨register, registerFound⟩
      have registerBound := (valid key register registerFound).2
      refine ⟨(sptMem_iff_lookup key _).mpr ⟨register, ?_⟩, ?_, ?_⟩
      · rw [sptLookup_sptInsert_ne name key next ssa same]
        exact registerFound
      · rw [sptLookup_sptInsert_ne name key next ssa same, registerFound]
        simp only [Option.getD_some]
        rw [sptLookup_sptInsert_ne next register value target (by omega)]
        simpa only [registerFound, Option.getD_some] using oldLookup
      · intro allocated
        have := oldBound allocated
        omega

/-- The adjacent original theorem has the identical generic tree statement;
its `stl`/`cstl` variables are locals maps, not full state carriers. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_locals_rel_set_var"]
theorem ssaLocalsRelSetVar {α : Type} (next : Nat) (ssa : Spt Nat)
    (source target : Spt α) (name : Nat) (value : α) :
    ssaLocalsRel next ssa source target ∧ ssaMapOK next ssa ∧ name < next →
      ssaLocalsRel (next + 4) (sptInsert name next ssa)
        (sptInsert name value source) (sptInsert next value target) :=
  ssaLocalsRelInsert next ssa source target name value

end Flapjack.Compiler.Backend.WordAlloc
