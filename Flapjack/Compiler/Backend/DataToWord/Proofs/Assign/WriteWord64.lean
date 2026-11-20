module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Word64Memory
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Ref
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.JoinEnvLocals
@[expose] public section

/-! Word64 allocation evaluator cases in the data-to-word assignment proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.SemanticPrimitivesHOL

namespace WriteWord64Witness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end WriteWord64Witness

/-- Specialize the reviewed Word64 memory allocation invariant to the evaluator payload.
This is proof infrastructure for `evaluate_WriteWord64`. -/
private theorem word64Alloc64 (conf : DataToWord.Config) (be : Bool) (ts space : Nat)
    (refs : Spt (BvlSem.Ref DataSem.Value))
    (store : HolFiniteMapExact WordStoreHOL (WordLocW 64))
    (mem : BitVec 64 → WordLocW 64) (domain : BitVec 64 → Bool)
    (vars : List (DataSem.Value × WordLocW 64)) (w header : BitVec 64)
    (rel : memoryRel conf be ts refs space store mem domain vars)
    (enough : 1 < space) (encoded : encodeHeader conf 3 1 = some header) :
    ∃ ne curr mem1, store.lookup .nextFree = some (.word ne) ∧
      store.lookup .currHeap = some (.word curr) ∧
      storeList ne [.word header, .word w] mem domain = some mem1 ∧
      memoryRel conf be ts refs (space - 2)
        (store.update (.nextFree, .word (ne + wordSemBytesInWord * (2 : BitVec 64)))) mem1 domain
        ((.word64 w, Build.makePtr conf (ne - curr) (0 : BitVec 64) 1) :: vars) := by
  have rep : (word64Rep w : HeapElement (WordLocW 64) (HeapTag × List (WordLocW 64))) =
      .dataElement [] 1 (.word64Tag, [.word w]) := by simp [word64Rep]
  have h := memoryRel_word64Alt conf be ts refs space store mem domain [] vars w [.word w] header
    (by simpa using rel) (by simp [goodDimindex]) (by simpa using rep) (by simpa using enough) (by simpa using encoded)
  simpa using h

/-- The generated 64-bit allocation sequence preserves the full memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "evaluate_WriteWord64"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)
  (write_word64_existential_inhabitants := [β._unused])]
theorem evaluateWriteWord64 {width : Nat} [NeZero width] {C F β : Type} [Nonempty β]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (be : Bool) (ts space : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (target : WordSemStateFiniteExact width C F)
    (sl : Spt Flapjack.Compiler.Backend.DataSem.Value) (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (src dest : Nat) (w header : BitVec width)
    (rel : memoryRel conf be ts refs space target.store target.memory target.mdomain
      (joinEnvLocals sl target.locals ++ vars))
    (readSrc : target.getVar src = some (.word w))
    (shiftBound : shiftLength conf < width) (srcNe : src ≠ 1) (enough : 1 < space)
    (widthIs : width = 64) (encoded : encodeHeader conf 3 1 = some header)
    (present : ∀ n, (sptLookup n sl).isSome → (sptLookup (adjustVar n) target.locals).isSome) :
    ∃ (nf : WordLocW width) (mem1 : BitVec width → WordLocW width)
      (locals1 : Spt (WordLocW width)) (_unused : β),
      WordSemStateFiniteExact.evaluate (writeWord64 conf header dest src) target =
        (none, {target with store := target.store.update (.nextFree, nf), memory := mem1, locals := locals1}) ∧
      memoryRel conf be ts refs (space - 2) (target.store.update (.nextFree, nf)) mem1 target.mdomain
        (joinEnvLocals (sptInsert dest (.word64 (w.setWidth 64)) sl) locals1 ++ vars) ∧
      (∀ n, (sptLookup n sl).isSome → (sptLookup (adjustVar n) locals1).isSome) ∧
      (sptLookup (adjustVar dest) locals1).isSome ∧ sptLookup 0 locals1 = sptLookup 0 target.locals := by
  subst width
  obtain ⟨ne, curr, mem1, nextFree, currHeap, stored, resultRel⟩ :=
    word64Alloc64 conf be ts space refs target.store target.memory target.mdomain
      (joinEnvLocals sl target.locals ++ vars) w header rel enough encoded
  have dom0 : target.mdomain ne = true := by
    by_contra h
    simp [storeList, h] at stored
  have dom1 : target.mdomain (ne + wordSemBytesInWord) = true := by
    by_contra h
    simp [storeList, dom0, h] at stored
  have memEq : mem1 = fun x => if x = ne + wordSemBytesInWord then .word w else
      if x = ne then .word header else target.memory x := by
    simpa [storeList, dom0, dom1] using stored.symm
  let ptr := Build.makePtr conf (ne - curr) (0 : BitVec 64) 1
  let tmp := sptInsert 3 (.word header) (sptInsert 1 (.word ne) target.locals)
  let locals1 := sptInsert (adjustVar dest) ptr tmp
  have relTmp : memoryRel conf be ts refs (space - 2)
      (target.store.update (.nextFree, .word (ne + wordSemBytesInWord * (2 : BitVec 64)))) mem1 target.mdomain
      ([(.word64 w, ptr)] ++ joinEnvLocals sl tmp ++ vars) := by
    simpa [ptr, tmp, joinEnvLocals_insertOdd, List.append_assoc] using resultRel
  have relFinal := memoryRel_insert conf be ts refs (space - 2)
      (target.store.update (.nextFree, .word (ne + wordSemBytesInWord * (2 : BitVec 64)))) mem1 target.mdomain
      (.word64 w) ptr sl tmp vars dest (by simpa [joinEnvLocals] using relTmp)
  refine ⟨.word (ne + wordSemBytesInWord * (2 : BitVec 64)), mem1, locals1, Classical.choice inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · have srcLookup : sptLookup src target.locals = some (.word w) := readSrc
    have diff : ne + (wordSemBytesInWord : BitVec 64) ≠ ne := by
      simp [wordSemBytesInWord]
    have memoryOrder : (fun x => if x = ne then .word header else
          if x = ne + wordSemBytesInWord then .word w else target.memory x) = mem1 := by
      rw [memEq]
      funext x
      by_cases h0 : x = ne <;> by_cases h1 : x = ne + wordSemBytesInWord <;> simp_all
    have shiftSmall : shiftLength conf - 3 < 64 := by omega
    have shiftMod : (shiftLength conf - 3) % (2 ^ 64) = shiftLength conf - 3 := by
      apply Nat.mod_eq_of_lt
      omega
    change (shiftLength conf - 3) % 18446744073709551616 = shiftLength conf - 3 at shiftMod
    have shiftNot : ¬ 64 ≤ shiftLength conf - 3 := Nat.not_le_of_gt shiftSmall
    simp [writeWord64, shiftN, wordListSeq, WordSemStateFiniteExact.evaluate,
      WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.getStore, WordSemStateFiniteExact.setVar,
      WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.memStore,
      WordSemStateFiniteExact.fixClock, wordOpHOL, wordOp, theWords,
      nextFree, currHeap, srcLookup, dom0, dom1, srcNe, locals1, tmp, ptr,
      Build.makePtr, HolFiniteMapExact.update, HolFiniteMapExact.updateEq,
      FUPDATE_HOL, sptLookup_sptInsert_same, sptLookup_sptInsert_ne,
      wordShiftHOL, wordShiftAmount, BitVec.toNat_ofNat, shiftMod, shiftNot, memoryOrder, OrOp.or, BitVec.or_zero, BitVec.mul_comm]
    funext key
    by_cases h : key = .nextFree
    · simp [FUPDATE_HOL, FUPDATE, h]
    · simp [FUPDATE_HOL, FUPDATE, h, Ne.symm h]
  · simpa [locals1, joinEnvLocals] using relFinal
  · intro n hn
    by_cases hnd : n = dest
    · subst n
      simp [locals1, sptLookup_sptInsert_same]
    · have nadj : adjustVar n ≠ adjustVar dest := by simp [adjustVar] at *; omega
      have odd1 : adjustVar n ≠ 1 := by simp [adjustVar]
      have odd3 : adjustVar n ≠ 3 := by simp [adjustVar]
      simpa [locals1, tmp, sptLookup_sptInsert_ne _ _ _ _ nadj,
        sptLookup_sptInsert_ne _ _ _ _ odd3, sptLookup_sptInsert_ne _ _ _ _ odd1] using present n hn
  · simp [locals1, sptLookup_sptInsert_same]
  · have destNe : (0 : Nat) ≠ adjustVar dest := by simp [adjustVar]
    simp [locals1, tmp, sptLookup_sptInsert_ne _ _ _ _ destNe, sptLookup_sptInsert_ne]

/-- Specialize the reviewed Word64 memory allocation invariant to the two-word evaluator payload.
This is proof infrastructure for `evaluate_WriteWord64_on_32`. -/
private theorem word64Alloc32 (conf : DataToWord.Config) (be : Bool) (ts space : Nat)
    (refs : Spt (BvlSem.Ref DataSem.Value))
    (store : HolFiniteMapExact WordStoreHOL (WordLocW 32))
    (mem : BitVec 32 → WordLocW 32) (domain : BitVec 32 → Bool)
    (vars : List (DataSem.Value × WordLocW 32)) (w : BitVec 64) (header : BitVec 32)
    (rel : memoryRel conf be ts refs space store mem domain vars)
    (enough : 2 < space) (encoded : encodeHeader conf 3 2 = some header) :
    ∃ ne curr mem1, store.lookup .nextFree = some (.word ne) ∧
      store.lookup .currHeap = some (.word curr) ∧
      storeList ne [.word header, .word ((w >>> 32).setWidth 32), .word (w.setWidth 32)] mem domain = some mem1 ∧
      memoryRel conf be ts refs (space - 3)
        (store.update (.nextFree, .word (ne + wordSemBytesInWord * (3 : BitVec 32)))) mem1 domain
        ((.word64 w, Build.makePtr conf (ne - curr) (0 : BitVec 32) 2) :: vars) := by
  have rep : (word64Rep w : HeapElement (WordLocW 32) (HeapTag × List (WordLocW 32))) =
      .dataElement [] 2 (.word64Tag, [.word ((w >>> 32).setWidth 32), .word (w.setWidth 32)]) := by simp [word64Rep]
  have h := memoryRel_word64Alt conf be ts refs space store mem domain [] vars w
    [.word ((w >>> 32).setWidth 32), .word (w.setWidth 32)] header
    (by simpa using rel) (by simp [goodDimindex]) (by simpa using rep) (by simpa using enough) (by simpa using encoded)
  simpa using h

/-- The generated 32-bit allocation sequence preserves the full memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "evaluate_WriteWord64_on_32"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)
  (write_word64_existential_inhabitants := [β._unused])]
theorem evaluateWriteWord64On32 {width : Nat} [NeZero width] {C F β : Type} [Nonempty β]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (be : Bool) (ts space : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (target : WordSemStateFiniteExact width C F)
    (sl : Spt Flapjack.Compiler.Backend.DataSem.Value) (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (src1 src2 dest : Nat) (w : BitVec 64) (header : BitVec width)
    (rel : memoryRel conf be ts refs space target.store target.memory target.mdomain
      (joinEnvLocals sl target.locals ++ vars))
    (readLow : target.getVar src1 = some (.word (w.setWidth width)))
    (readHigh : target.getVar src2 = some (.word ((w >>> 32).setWidth width)))
    (shiftBound : shiftLength conf < width) (src1Ne : src1 ≠ 1) (src2Ne : src2 ≠ 1)
    (enough : 2 < space) (widthIs : width = 32) (encoded : encodeHeader conf 3 2 = some header)
    (present : ∀ n, (sptLookup n sl).isSome → (sptLookup (adjustVar n) target.locals).isSome) :
    ∃ (nf : WordLocW width) (mem1 : BitVec width → WordLocW width)
      (locals1 : Spt (WordLocW width)) (_unused : β),
      WordSemStateFiniteExact.evaluate (writeWord64On32 conf header dest src1 src2) target =
        (none, {target with store := target.store.update (.nextFree, nf), memory := mem1, locals := locals1}) ∧
      memoryRel conf be ts refs (space - 3) (target.store.update (.nextFree, nf)) mem1 target.mdomain
        (joinEnvLocals (sptInsert dest (.word64 w) sl) locals1 ++ vars) ∧
      (∀ n, (sptLookup n sl).isSome → (sptLookup (adjustVar n) locals1).isSome) ∧
      (sptLookup (adjustVar dest) locals1).isSome ∧ sptLookup 0 locals1 = sptLookup 0 target.locals := by
  subst width
  obtain ⟨ne, curr, mem1, nextFree, currHeap, stored, resultRel⟩ :=
    word64Alloc32 conf be ts space refs target.store target.memory target.mdomain
      (joinEnvLocals sl target.locals ++ vars) w header rel enough encoded
  have dom0 : target.mdomain ne = true := by
    by_contra h
    simp [storeList, h] at stored
  have dom1 : target.mdomain (ne + wordSemBytesInWord) = true := by
    by_contra h
    simp [storeList, dom0, h] at stored
  have dom2 : target.mdomain (ne + wordSemBytesInWord + wordSemBytesInWord) = true := by
    by_contra h
    simp [storeList, dom0, dom1, h] at stored
  have memEq : mem1 = fun x =>
      if x = ne + wordSemBytesInWord + wordSemBytesInWord then .word (w.setWidth 32)
      else if x = ne + wordSemBytesInWord then .word ((w >>> 32).setWidth 32)
      else if x = ne then .word header else target.memory x := by
    simpa [storeList, dom0, dom1, dom2] using stored.symm
  let ptr := Build.makePtr conf (ne - curr) (0 : BitVec 32) 2
  let tmp := sptInsert 3 (.word header) (sptInsert 1 (.word ne) target.locals)
  let locals1 := sptInsert (adjustVar dest) ptr tmp
  have relTmp : memoryRel conf be ts refs (space - 3)
      (target.store.update (.nextFree, .word (ne + wordSemBytesInWord * (3 : BitVec 32)))) mem1 target.mdomain
      ([(.word64 w, ptr)] ++ joinEnvLocals sl tmp ++ vars) := by
    simpa [ptr, tmp, joinEnvLocals_insertOdd, List.append_assoc] using resultRel
  have relFinal := memoryRel_insert conf be ts refs (space - 3)
      (target.store.update (.nextFree, .word (ne + wordSemBytesInWord * (3 : BitVec 32)))) mem1 target.mdomain
      (.word64 w) ptr sl tmp vars dest (by simpa [joinEnvLocals] using relTmp)
  refine ⟨.word (ne + wordSemBytesInWord * (3 : BitVec 32)), mem1, locals1, Classical.choice inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · have lowLookup : sptLookup src1 target.locals = some (.word (w.setWidth 32)) := readLow
    have highLookup : sptLookup src2 target.locals = some (.word ((w >>> 32).setWidth 32)) := readHigh
    have d01 : ne + (wordSemBytesInWord : BitVec 32) ≠ ne := by simp [wordSemBytesInWord]
    have d02 : ne + (wordSemBytesInWord : BitVec 32) + wordSemBytesInWord ≠ ne := by
      simp [wordSemBytesInWord, BitVec.add_assoc]
    have memoryOrder : (fun x => if x = ne then .word header else
          if x = ne + wordSemBytesInWord + wordSemBytesInWord then .word (w.setWidth 32) else
          if x = ne + wordSemBytesInWord then .word ((w >>> 32).setWidth 32) else target.memory x) = mem1 := by
      rw [memEq]
      funext x
      by_cases h0 : x = ne <;> by_cases h1 : x = ne + wordSemBytesInWord <;>
        by_cases h2 : x = ne + wordSemBytesInWord + wordSemBytesInWord <;> simp_all
    have shiftSmall : shiftLength conf - 2 < 32 := by omega
    have shiftMod : (shiftLength conf - 2) % (2 ^ 32) = shiftLength conf - 2 := by
      apply Nat.mod_eq_of_lt
      omega
    change (shiftLength conf - 2) % 4294967296 = shiftLength conf - 2 at shiftMod
    have shiftNot : ¬ 32 ≤ shiftLength conf - 2 := Nat.not_le_of_gt shiftSmall
    simp [wordSemBytesInWord, BitVec.add_assoc] at dom1 dom2 memoryOrder
    simp [writeWord64On32, shiftN, wordListSeq, WordSemStateFiniteExact.evaluate,
      WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.getStore, WordSemStateFiniteExact.setVar,
      WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.memStore,
      WordSemStateFiniteExact.fixClock, wordOpHOL, wordOp, theWords,
      nextFree, currHeap, lowLookup, highLookup, dom0, dom1, dom2, src1Ne, src2Ne, locals1, tmp, ptr,
      Build.makePtr, HolFiniteMapExact.update, HolFiniteMapExact.updateEq,
      FUPDATE_HOL, sptLookup_sptInsert_same, sptLookup_sptInsert_ne,
      wordShiftHOL, wordShiftAmount, BitVec.toNat_ofNat, shiftMod, shiftNot, memoryOrder,
      OrOp.or, BitVec.or_zero, BitVec.mul_comm, wordSemBytesInWord]
    funext key
    by_cases h : key = .nextFree
    · simp [FUPDATE_HOL, FUPDATE, h]
    · simp [FUPDATE_HOL, FUPDATE, h, Ne.symm h]
  · simpa [locals1, joinEnvLocals] using relFinal
  · intro n hn
    by_cases hnd : n = dest
    · subst n
      simp [locals1, sptLookup_sptInsert_same]
    · have nadj : adjustVar n ≠ adjustVar dest := by simp [adjustVar] at *; omega
      have odd1 : adjustVar n ≠ 1 := by simp [adjustVar]
      have odd3 : adjustVar n ≠ 3 := by simp [adjustVar]
      simpa [locals1, tmp, sptLookup_sptInsert_ne _ _ _ _ nadj,
        sptLookup_sptInsert_ne _ _ _ _ odd3, sptLookup_sptInsert_ne _ _ _ _ odd1] using present n hn
  · simp [locals1, sptLookup_sptInsert_same]
  · have destNe : (0 : Nat) ≠ adjustVar dest := by simp [adjustVar]
    simp [locals1, tmp, sptLookup_sptInsert_ne _ _ _ _ destNe, sptLookup_sptInsert_ne]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
