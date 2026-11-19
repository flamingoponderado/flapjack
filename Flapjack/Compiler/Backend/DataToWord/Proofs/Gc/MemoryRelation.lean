module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.WordMlInvInsert

@[expose] public section

/-! Data-to-word memory relation updates used by the GC proof. -/
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

/-- Inserting a represented pair into both local trees preserves the full
memory relation when that pair is already among its roots. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "memory_rel_insert"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem memoryRel_insert {width : Nat} [NeZero width] (c : Config) (be : Bool) (ts : Nat)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (x : DataSem.Value) (w : WordLocW width) (d : Spt DataSem.Value)
    (l : Spt (WordLocW width)) (xs : List (DataSem.Value × WordLocW width)) (dest : Nat)
    (rel : memoryRel c be ts refs sp st m dm
      ([(x, w)] ++ joinEnv d (sptToAList (sptInter l (adjustSet d))) ++ xs)) :
    memoryRel c be ts refs sp st m dm
      (joinEnv (sptInsert dest x d)
        (sptToAList (sptInter (sptInsert (adjustVar dest) w l)
          (adjustSet (sptInsert dest x d)))) ++ xs) := by
  obtain ⟨heap, limit, a, sp1, sp2, gens, memory, inv, bound, space⟩ := rel
  exact ⟨heap, limit, a, sp1, sp2, gens, memory,
    wordMlInv_insert heap be a sp1 sp2 gens limit ts c refs d l dest x w xs inv, bound, space⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
