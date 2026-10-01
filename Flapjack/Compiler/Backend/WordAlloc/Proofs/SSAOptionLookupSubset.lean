import Flapjack.Compiler.Backend.WordAlloc.SSAFixInconsistencies

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Full native option-lookup subset helper. The target locals payload stays
generic, independently of the natural-register SSA map. Both original domain
premises and the complete mapped-list subset conclusion are retained. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "option_lookup_subset_helper"]
theorem optionLookupSubsetHelper {α : Type} (ssa : Spt Nat) (target : Spt α)
    (names : List Nat)
    (h : (∀ key register, sptLookup key ssa = some register → sptDomain target register) ∧
      (∀ key ∈ names, sptDomain ssa key)) :
    ∀ register ∈ names.map (optionLookup ssa), sptDomain target register := by
  intro register member
  rcases List.mem_map.mp member with ⟨key, keyMember, rfl⟩
  rcases (sptMem_iff_lookup key ssa).mp (h.2 key keyMember) with ⟨value, found⟩
  simpa only [optionLookup, found] using h.1 key value found

end Flapjack.Compiler.Backend.WordAlloc
