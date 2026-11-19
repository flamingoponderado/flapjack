module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation

@[expose] public section

/-! Temporary-store updates preserve the data-to-word memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- The memory invariant does not observe temporary store entries. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "memory_rel_Temp"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec), simp]
theorem memoryRel_temp {width : Nat} [NeZero width] (c : Config) (be : Bool) (ts : Nat)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (i : BitVec 5) (w : WordLocW width)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (vars : List (DataSem.Value × WordLocW width)) :
    memoryRel c be ts refs sp (st.updateEq (.temp i, w)) m dm vars ↔
      memoryRel c be ts refs sp st m dm vars := by
  simp [memoryRel, heapInMemoryStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
