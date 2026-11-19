module

public import Flapjack.Compiler.Backend.Semantics.WordSem.EnvListSupport

@[expose] public section

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend

/-- Converting a word environment to a list preserves its domain. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "env_to_list_domain"
  (words_as_type_indexed_bitvec)]
theorem envToList_domain {width : Nat} [NeZero width]
    (env : Spt (WordLocW width)) (p : Nat → Nat → Nat)
    (entries : List (Nat × WordLocW width)) (permute : Nat → Nat → Nat)
    (run : wordSemEnvToList env p = (entries, permute)) :
    sptDomain (sptFromAList entries) = sptDomain env := by
  have equiv := (wordSemEnvToListLookupEquiv env p entries permute run).1
  funext key
  apply propext
  simp [sptDomain, sptLookup_sptFromAList, equiv key]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
