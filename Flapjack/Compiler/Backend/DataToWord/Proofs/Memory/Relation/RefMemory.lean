module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ConcreteRefAlloc
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.FreshRefProof
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Word64Memory

@[expose] public section

/-! Concrete memory correspondence for fresh reference allocation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.GcCombined

/-- Allocating a fresh value-array reference preserves the complete memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Ref"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem memoryRel_ref {width : Nat} {tagWidth : Nat} [NeZero width] [NeZero tagWidth] (c : Flapjack.Compiler.Backend.DataToWord.Config) (be : Bool)
    (ts : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (sp : Nat) (st : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (vals : List Flapjack.Compiler.Backend.DataSem.Value) (ws : List (WordLocW width))
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (hd : BitVec width) (new : Nat)
    (rel : memoryRel c be ts refs sp st m dm (vals.zip ws ++ vars))
    (lens : vals.length = ws.length) (encoded : DataToWord.encodeHeader c 2 ws.length = some hd)
    (fresh : ¬ sptDomain refs new) (enough : ws.length < sp) (good : goodDimindex width) :
    ∃ eoh curr trig m1, st.lookup .endOfHeap = some (.word eoh) ∧
      st.lookup .triggerGC = some (.word trig) ∧ st.lookup .currHeap = some (.word curr) ∧
      storeList (eoh - wordSemBytesInWord * BitVec.ofNat width (ws.length + 1)) (.word hd :: ws) m dm = some m1 ∧
      memoryRel c be ts (sptInsert new (.valueArray vals) refs) (sp - (ws.length + 1))
        ((st.update (.endOfHeap, .word (eoh - wordSemBytesInWord * BitVec.ofNat width (ws.length + 1)))).update
          (.triggerGC, .word (trig - wordSemBytesInWord * BitVec.ofNat width (ws.length + 1)))) m1 dm
        ((.refPtr true new, Build.makePtr c ((eoh - wordSemBytesInWord * BitVec.ofNat width (ws.length + 1)) - curr) (0 : BitVec tagWidth) ws.length) :: vars) := by
  obtain ⟨heap, limit, a, sp0, sp1, gens, heapMem, wordInv, limitBound, spaceBound⟩ := rel
  obtain ⟨roots, absInv, addresses⟩ := wordInv
  have absInv1 : absMlInv c (vals ++ vars.map Prod.fst) refs
      (roots, heap, be, a, sp0, sp1, gens) limit ts := by
    simpa [List.map_append, List.map_fst_zip (Nat.le_of_eq lens)] using absInv
  obtain ⟨_, rs, roots2, heap2, rootsEq, rootsLen, stored, absAfter⟩ :=
    newRef (β := Unit) c vals (vars.map Prod.fst) refs roots heap be a sp0 sp1 gens limit ts new
      ⟨absInv1, fresh, by omega⟩
  have addrMap : roots.map (wordAddr c) = ws ++ vars.map Prod.snd := by
    have h := (every2_function_eq roots ((vals.zip ws ++ vars).map Prod.snd) (wordAddr c)).mp addresses
    simpa [List.map_append, List.map_snd_zip (Nat.le_of_eq lens.symm)] using h
  rw [rootsEq, List.map_append] at addrMap
  have ⟨mapped, tailMap⟩ := List.append_inj addrMap (by simp [rootsLen, lens])
  obtain ⟨eoh, trig, curr, m1, endLookup, triggerLookup, currLookup, eohEq, run, heapMem1⟩ :=
    heapInMemoryStore_allocateRef c heap heap2 a sp0 sp1 gens st m dm limit rs ws hd mapped encoded good
      absInv1.2.2.2.1 (by omega) stored heapMem
  let offset := a + sp0 + sp1 - (ws.length + 1)
  have absPopped : absMlInv c (.refPtr true new :: vars.map Prod.fst) (sptInsert new (.valueArray vals) refs)
      (.pointer offset (.word 0) :: roots2, heap2, be, a, sp0 - (ws.length + 1), sp1, gens) limit ts := by
    apply popThm c vals (.refPtr true new :: vars.map Prod.fst) _ rs _ heap2 be a (sp0 - (ws.length + 1)) sp1 gens limit ts
    exact ⟨by simpa [offset, lens] using absAfter, rootsLen.symm⟩
  have ptrEq : wordAddr c (.pointer offset (.word 0)) =
      Build.makePtr c ((eoh - wordSemBytesInWord * BitVec.ofNat width (ws.length + 1)) - curr) (0 : BitVec tagWidth) ws.length := by
    have stride : StackRemove.bytesInWord width * BitVec.ofNat width offset =
        (BitVec.ofNat width offset <<< wordShiftAmount width) := by
      rcases good with h | h <;> subst width <;> apply BitVec.eq_of_toNat_eq <;>
        simp [StackRemove.bytesInWord, wordShiftAmount, BitVec.toNat_mul,
          BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mul_comm, Nat.mul_mod]
    have boundary : a + sp0 + sp1 = offset + (ws.length + 1) := by dsimp [offset]; omega
    have delta : (eoh - wordSemBytesInWord * BitVec.ofNat width (ws.length + 1)) - curr =
        StackRemove.bytesInWord width * BitVec.ofNat width offset := by
      rw [eohEq, boundary]
      simp [wordSemBytesInWord, StackRemove.bytesInWord, BitVec.ofNat_add, BitVec.mul_add, ← BitVec.add_assoc]
    have shifts : wordShiftAmount width + (shiftLength c - wordShiftAmount width) = shiftLength c := by
      have h := heapMem.2.2.1
      omega
    simp only [Build.makePtr, delta, stride, ← BitVec.shiftLeft_add, shifts, wordAddr, getAddr, getLowerBits]
    simp
  have afterRoots : List.Forall₂ (fun address word => wordAddr c address = word) roots2 (vars.map Prod.snd) :=
    (every2_function_eq roots2 (vars.map Prod.snd) (wordAddr c)).mpr tailMap
  have wordInv1 : wordMlInv (heap2, be, a, sp0 - (ws.length + 1), sp1, gens) limit ts c
      (sptInsert new (.valueArray vals) refs)
      ((.refPtr true new, Build.makePtr c ((eoh - wordSemBytesInWord * BitVec.ofNat width (ws.length + 1)) - curr) (0 : BitVec tagWidth) ws.length) :: vars) := by
    refine ⟨.pointer offset (.word 0) :: roots2, absPopped, ?_⟩
    simp only [List.map_cons]
    exact List.Forall₂.cons ptrEq afterRoots
  refine ⟨eoh, curr, trig, m1, endLookup, triggerLookup, currLookup, run, ?_⟩
  exact ⟨heap2, limit, a, sp0 - (ws.length + 1), sp1, gens, heapMem1, wordInv1, limitBound, by omega⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
