module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ConcreteAlloc
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ConcreteLeafAlloc

@[expose] public section

/-! Concrete reference allocation for HOL `memory_rel_Ref`. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.GcCombined

/-- Store the concrete reference block and update both free-space boundaries.
This Flapjack helper supplies the concrete heap-store step of HOL `memory_rel_Ref`. -/
theorem heapInMemoryStore_allocateRef {width : Nat} [NeZero width]
    (c : DataToWord.Config) (heap heap2 : ValueHeap width) (a sp sp1 : Nat) (gens : GenState)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool) (limit : Nat)
    (rs : List (HeapAddress (WordLocW width))) (ws : List (WordLocW width)) (hd : BitVec width)
    (mapped : rs.map (wordAddr c) = ws) (encoded : encodeHeader c 2 ws.length = some hd)
    (good : goodDimindex width) (unused : unusedSpaceInv a (sp + sp1) heap) (fits : ws.length + 1 ≤ sp)
    (stored : heapStoreUnused a (sp + sp1) (refBlock rs) heap = (heap2, true))
    (heapMem : heapInMemoryStore heap a sp sp1 gens c st m dm limit) :
    ∃ eoh trig curr m1, st.lookup .endOfHeap = some (.word eoh) ∧
      st.lookup .triggerGC = some (.word trig) ∧ st.lookup .currHeap = some (.word curr) ∧
      eoh = curr + StackRemove.bytesInWord width * BitVec.ofNat width (a + sp + sp1) ∧
      storeList (eoh - wordSemBytesInWord * BitVec.ofNat width (ws.length + 1)) (.word hd :: ws) m dm = some m1 ∧
      heapInMemoryStore heap2 a (sp - (ws.length + 1)) sp1 gens c
        ((st.update (.endOfHeap, .word (eoh - wordSemBytesInWord * BitVec.ofNat width (ws.length + 1)))).update
          (.triggerGC, .word (trig - wordSemBytesInWord * BitVec.ofNat width (ws.length + 1)))) m1 dm limit := by
  have sizes : rs.length = ws.length := by have h := congrArg List.length mapped; simpa using h
  have positive : sp + sp1 ≠ 0 := by omega
  have found := unused.1 positive
  obtain ⟨pre, post, heapShape, aEq⟩ := heapLookup_split heap a _ found
  have expand : (heapExpand (sp + sp1) : ValueHeap width) = [.unused (sp + sp1 - 1)] := by
    unfold heapExpand
    rw [if_neg positive]
  have heapOld : heap = pre ++ heapExpand (sp + sp1) ++ post := by
    simpa [expand, List.append_assoc] using heapShape
  have heap2Shape : heap2 = pre ++ heapExpand (sp + sp1 - (ws.length + 1)) ++ [refBlock rs] ++ post := by
    have store := stored
    classical
    simp only [heapStoreUnused, found, show elLength (refBlock rs : HeapElement (WordLocW width) (HeapTag × List (WordLocW width))) ≤ sp + sp1 by simp [refBlock, elLength, sizes]; omega,
      and_self, ↓reduceIte] at store
    rw [heapShape, aEq, heapStore_atPrefix] at store
    have h := congrArg Prod.fst store
    simpa [refBlock, elLength, sizes, List.append_assoc] using h.symm
  obtain ⟨heapBound, byteBound, shiftBound, lenPos, lenBound, shiftWidth, globals, curr, other,
    currAligned, otherAligned, currLookup, otherLookup, freeLookup, triggerLookup, endLookup,
    heapLenLookup, globInv, genInv, heapSep⟩ := heapMem
  have heapSepOld : SetSep.star (wordHeap curr (pre ++ heapExpand (sp + sp1) ++ post) c)
      (wordHeap other (heapExpand limit) c) (SetSep.fun2Set (m, fun x => dm x = true)) := by simpa [heapOld] using heapSep
  have configBound : c.lenSize + 5 < width := by omega
  obtain ⟨m1, run, heapSepNew⟩ := wordHeapAllocEnd c curr pre post (sp + sp1) (refBlock rs) ws hd
    (wordHeap other (heapExpand limit) c) m dm (by omega) (by simp [refBlock, elLength, sizes])
    (fun addr => wordElRefEq c addr rs ws hd mapped encoded configBound good) heapSepOld
  have nLen : heapLength heap2 = heapLength heap := heapStoreUnused_imp_length a (sp + sp1) (refBlock rs) heap heap2 stored
  let eoh := curr + StackRemove.bytesInWord width * BitVec.ofNat width (a + sp + sp1)
  let trig := curr + StackRemove.bytesInWord width * BitVec.ofNat width (a + sp)
  let step := wordSemBytesInWord * BitVec.ofNat width (ws.length + 1)
  let st1 := (st.update (.endOfHeap, .word (eoh - step))).update (.triggerGC, .word (trig - step))
  have boundary : a + sp + sp1 = (a + sp + sp1 - (ws.length + 1)) + (ws.length + 1) := by omega
  have boundaryTrig : a + sp = (a + (sp - (ws.length + 1))) + (ws.length + 1) := by omega
  have newEnd : eoh - step = curr + StackRemove.bytesInWord width * BitVec.ofNat width (a + sp + sp1 - (ws.length + 1)) := by
    conv_lhs => unfold eoh step
    rw [boundary]
    simp [wordSemBytesInWord, StackRemove.bytesInWord, BitVec.ofNat_add, BitVec.mul_add, ← BitVec.add_assoc]
  have newTrig : trig - step = curr + StackRemove.bytesInWord width * BitVec.ofNat width (a + (sp - (ws.length + 1))) := by
    conv_lhs => unfold trig step
    rw [boundaryTrig]
    simp [wordSemBytesInWord, StackRemove.bytesInWord, BitVec.ofNat_add, BitVec.mul_add, ← BitVec.add_assoc]
  have shapeSep : SetSep.star (wordHeap curr heap2 c) (wordHeap other (heapExpand limit) c)
      (SetSep.fun2Set (m1, fun x => dm x = true)) := by simpa [heap2Shape] using heapSepNew
  have heapMem1 : heapInMemoryStore heap2 a (sp - (ws.length + 1)) sp1 gens c st1 m1 dm limit := by
    refine ⟨by simpa [nLen] using heapBound, by simpa [nLen] using byteBound, shiftBound, lenPos, lenBound, shiftWidth, ?_, curr, other,
      currAligned, otherAligned, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, shapeSep⟩
    · simpa [st1, HolFiniteMapExact.update, FUPDATE] using globals
    · simpa [st1, HolFiniteMapExact.update, FUPDATE] using currLookup
    · simpa [st1, HolFiniteMapExact.update, FUPDATE] using otherLookup
    · simpa [st1, HolFiniteMapExact.update, FUPDATE] using freeLookup
    · simp [st1, HolFiniteMapExact.update, FUPDATE, newTrig]
    · have arith : a + (sp - (ws.length + 1)) + sp1 = a + sp + sp1 - (ws.length + 1) := by omega
      simp [st1, HolFiniteMapExact.update, FUPDATE, newEnd, arith]
    · simpa [st1, HolFiniteMapExact.update, FUPDATE] using heapLenLookup
    · simpa [st1, HolFiniteMapExact.update, FUPDATE] using globInv
    · simpa [st1, HolFiniteMapExact.update, FUPDATE] using genInv
  refine ⟨eoh, trig, curr, m1, ?_, ?_, currLookup, rfl, ?_, ?_⟩
  · simpa [eoh, Nat.add_assoc] using endLookup
  · simpa [trig] using triggerLookup
  · simpa [step, newEnd, aEq, Nat.add_assoc] using run
  · exact heapMem1

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
