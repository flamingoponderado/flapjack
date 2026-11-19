module

public import Flapjack.HolRef
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Image

@[expose] public section

/-!
# Memory-domain lemmas of HOL `word_elimProof`

Counterpart of `cakeml/compiler/backend/proofs/word_elimProofScript.sml:289-352`:
the `get_memory` and `find_loc_state` group.  `FINITE_mdom_mem` is the one
lemma in this group that does not mention the `SET_TO_LIST` enumeration used by
`get_memory`, whose rendering is still an open decision, so the other lemmas of
the group (`domain_get_memory`, `get_memory_update`, `domain_find_loc_state`,
`get_memory_write_bytearray_lemma`) stay untagged for now.
-/

namespace Flapjack.Compiler.Backend.WordElim

/-- Exact HOL `FINITE_mdom_mem` (`word_elimProofScript.sml:297-305`): the image
    of a finite memory domain under the memory function is finite.  HOL
    quantifies `mdom` and leaves `mem` free; the binder order follows the typed
    capture (`mdom`, then the free `mem`, as for the free `lsz` of
    `get_stack_hd_thm`), and HOL's set comprehension `{mem x | x ∈ mdom}` is the
    reviewed `Set.image` rendering. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "FINITE_mdom_mem"]
theorem finiteMdomMem {α β : Type} (mdom : Set α) (mem : α → β) :
    Set.Finite mdom → Set.Finite (Set.image mem mdom) :=
  fun h => h.image mem

end Flapjack.Compiler.Backend.WordElim
