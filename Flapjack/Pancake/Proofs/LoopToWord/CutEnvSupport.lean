import Flapjack.Compiler.Backend.Semantics.WordSem.EnvListSupport

namespace Flapjack.LoopToWord

open Flapjack

/-- Exact HOL `loop_to_wordProofScript.sml:536-541` `env_to_list_LN_IMP`:
`env_to_list LN l = (x,p) ==> x = []`, where HOL `env_to_list` is rendered by
the tagged `Flapjack.wordSemEnvToList` (`wordSemScript.sml:507-515`), `LN` by
the empty `Spt`, and HOL's indexed word dimension by `WordLocW width`. The
empty environment has no `toAList` entries, and `env_to_list`'s sort/rearrange
stages preserve membership, so the emitted list is empty. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "env_to_list_LN_IMP"
  (words_as_type_indexed_bitvec)]
theorem envToListLNIMPHOL {width : Nat} [NeZero width]
    (bijSeq : Nat → Nat → Nat) (x : List (Nat × WordLocW width))
    (p : Nat → Nat → Nat)
    (h : wordSemEnvToList (.ln : Spt (WordLocW width)) bijSeq = (x, p)) :
    x = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro entry hmem
  have hmem' : entry ∈ (wordSemEnvToList (.ln : Spt (WordLocW width)) bijSeq).1 := by
    rw [h]; exact hmem
  have hmemSource :=
    (wordSemEnvToList_mem_iff (.ln : Spt (WordLocW width)) bijSeq entry).mp hmem'
  simp at hmemSource

end Flapjack.LoopToWord
