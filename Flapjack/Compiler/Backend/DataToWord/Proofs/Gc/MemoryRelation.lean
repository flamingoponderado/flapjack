module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.WordMlInvInsert
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.WordMlInvGetVars

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

namespace MemoryRelationWitnesses

/-- Canonical target-state roundtrip for relations with a standalone map. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end MemoryRelationWitnesses

/-- Reading corresponding local lists preserves the full memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "memory_rel_get_vars_IMP_lemma"
  (fmap_as_finite_support_relation := [st, WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem memoryRel_getVars_aux {width : Nat} [NeZero width] {C F : Type}
    (c : Config) (be : Bool) (ts : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (sp : Nat) (st : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (ll : Spt Flapjack.Compiler.Backend.DataSem.Value) (t : WordSemStateFiniteExact width C F)
    (envs : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (n : List Nat)
    (x : List Flapjack.Compiler.Backend.DataSem.Value) (w : List (WordLocW width))
    (h : memoryRel c be ts refs sp st m dm
       (joinEnv ll (sptToAList (sptInter t.locals (adjustSet ll))) ++ envs) ∧
      DataSem.getVars n ll = some x ∧
      WordSemStateFiniteExact.getVars (n.map adjustVar) t = some w) :
    memoryRel c be ts refs sp st m dm
      (x.zip w ++ joinEnv ll (sptToAList (sptInter t.locals (adjustSet ll))) ++ envs) := by
  obtain ⟨rel, dataRead, wordRead⟩ := h
  obtain ⟨heap, limit, a, sp1, sp2, gens, mem, inv, bound, space⟩ := rel
  exact ⟨heap, limit, a, sp1, sp2, gens, mem,
    wordMlInv_getVars heap be a sp1 sp2 gens limit ts c refs ll t n x w envs ⟨inv, dataRead, wordRead⟩,
    bound, space⟩
/-- Reading corresponding state locals preserves the full memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "memory_rel_get_vars_IMP"
  (fmap_as_finite_support_relation := [st, WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem memoryRel_getVars {width : Nat} [NeZero width] {C F : Type}
    (c : Config) (be : Bool) (ts : Nat) (s : Flapjack.Compiler.Backend.DataSem.State C F)
    (sp : Nat) (st : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (t : WordSemStateFiniteExact width C F) (envs : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (n : List Nat) (x : List Flapjack.Compiler.Backend.DataSem.Value) (w : List (WordLocW width))
    (h : memoryRel c be ts s.refs sp st m dm
       (joinEnv s.locals (sptToAList (sptInter t.locals (adjustSet s.locals))) ++ envs) ∧
      DataSem.getVars n s.locals = some x ∧
      WordSemStateFiniteExact.getVars (n.map adjustVar) t = some w) :
    memoryRel c be ts s.refs sp st m dm
      (x.zip w ++ joinEnv s.locals (sptToAList (sptInter t.locals (adjustSet s.locals))) ++ envs) :=
  memoryRel_getVars_aux c be ts s.refs sp st m dm s.locals t envs n x w h

/-- Reading a corresponding local pair preserves the full memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "memory_rel_get_var_IMP"
  (fmap_as_finite_support_relation := [st, WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem memoryRel_getVar {width : Nat} [NeZero width] {C F : Type}
    (u ts : Nat) (t : WordSemStateFiniteExact width C F)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (sp : Nat)
    (s : Flapjack.Compiler.Backend.DataSem.State C F) (m : BitVec width → WordLocW width)
    (envs : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (dm : BitVec width → Bool)
    (c : Config) (be : Bool) (y : Flapjack.Compiler.Backend.DataSem.Value) (y' : WordLocW width)
    (h : memoryRel c be ts s.refs sp st m dm
       (joinEnv s.locals (sptToAList (sptInter t.locals (adjustSet s.locals))) ++ envs) ∧
      DataSem.getVar u s.locals = some y ∧
      WordSemStateFiniteExact.getVar (adjustVar u) t = some y') :
    memoryRel c be ts s.refs sp st m dm
      ((y, y') :: (joinEnv s.locals (sptToAList (sptInter t.locals (adjustSet s.locals))) ++ envs)) := by
  obtain ⟨rel, dataRead, wordRead⟩ := h
  have dataReads : DataSem.getVars [u] s.locals = some [y] := by simp [DataSem.getVars, dataRead]
  have wordReads : WordSemStateFiniteExact.getVars ([u].map adjustVar) t = some [y'] := by
    simp [WordSemStateFiniteExact.getVars, wordRead]
  simpa using memoryRel_getVars c be ts s sp st m dm t envs [u] [y] [y'] ⟨rel, dataReads, wordReads⟩
end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
