module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.BasicLemmas
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.RealAddress
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.ShiftVar
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockStack
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockHeader
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Number
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Rearrange
public import Flapjack.Compiler.Backend.Semantics.DataSem.Conversions
public import Flapjack.Compiler.Backend.DataToWord.Stubs
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Word64
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.SmallWordLemmas
public import Flapjack.Compiler.Backend.WordToStack.Proofs.CallLocalRecovery

@[expose] public section

/-! The code- and data-installation loops of `data_to_word_assignProofScript.sml`
(`InstallCode_code_thm`, lines 1845-1962, and `InstallData_code_thm`, lines
1969-2096). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum

namespace InstallStubsWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end InstallStubsWitness

/-- Branch on the low bit of a word variable, as the installation loops do;
local proof infrastructure for the HOL loop proofs. -/
theorem installEvalTestOne {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (r : Nat) (w : BitVec width)
    (c1 c2 : WordLangProgHOL (BitVec width)) (read : s.getVar r = some (.word w)) :
    WordSemStateFiniteExact.evaluate (.ite .test r (.imm 1) c1 c2) s =
      if w.getLsbD 0 then WordSemStateFiniteExact.evaluate c2 s
      else WordSemStateFiniteExact.evaluate c1 s := by
  have key : (AndOp.and w (1#width) == 0#width) = !w.getLsbD 0 := by
    change (w &&& 1#width == 0#width) = _
    have := wordBitTest0 w
    rw [BitVec.and_comm] at this
    cases hb : w.getLsbD 0 <;> simp_all
  simp [WordSemStateFiniteExact.evaluate, read, WordSemStateFiniteExact.getVarImm,
    wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, key]
  cases w.getLsbD 0 <;> simp

/-- Lookup after insertion, by cases on the key. -/
theorem installLookupInsert {α : Type} (k k' : Nat) (v : α) (tree : Spt α) :
    sptLookup k (sptInsert k' v tree) = if k = k' then some v else sptLookup k tree := by
  by_cases h : k = k'
  · subst h; simp [sptLookup_sptInsert_same]
  · simp [h, sptLookup_sptInsert_ne k' k v tree h]

/-- Execute an assignment before its continuation. -/
theorem installSeqAssign {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (key : Nat) (expr : WordLangExpHOL (BitVec width))
    (v : WordLocW width) (tail : WordLangProgHOL (BitVec width))
    (read : s.wordExp expr = some v) :
    WordSemStateFiniteExact.evaluate (.seq (.assign key expr) tail) s =
      WordSemStateFiniteExact.evaluate tail (s.setVar key v) := by
  simp [WordSemStateFiniteExact.evaluate, read, WordSemStateFiniteExact.fixClock,
    WordSemStateFiniteExact.setVar]

/-- Write the code buffer before a continuation. -/
theorem installSeqCodeBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (r1 r2 : Nat) (w1 w2 : BitVec width)
    (cb : WordSemBuffer width 8) (tail : WordLangProgHOL (BitVec width))
    (h1 : s.getVar r1 = some (.word w1)) (h2 : s.getVar r2 = some (.word w2))
    (hw : wordSemBufferWrite s.codeBuffer w1 (w2.setWidth 8) = some cb) :
    WordSemStateFiniteExact.evaluate (.seq (.codeBufferWrite r1 r2) tail) s =
      WordSemStateFiniteExact.evaluate tail { s with codeBuffer := cb } := by
  simp [WordSemStateFiniteExact.evaluate, h1, h2, hw, WordSemStateFiniteExact.fixClock]

/-- Write the data buffer before a continuation. -/
theorem installSeqDataBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (r1 r2 : Nat) (w1 w2 : BitVec width)
    (db : WordSemBuffer width width) (tail : WordLangProgHOL (BitVec width))
    (h1 : s.getVar r1 = some (.word w1)) (h2 : s.getVar r2 = some (.word w2))
    (hw : wordSemBufferWrite s.dataBuffer w1 w2 = some db) :
    WordSemStateFiniteExact.evaluate (.seq (.dataBufferWrite r1 r2) tail) s =
      WordSemStateFiniteExact.evaluate tail { s with dataBuffer := db } := by
  simp [WordSemStateFiniteExact.evaluate, h1, h2, hw, WordSemStateFiniteExact.fixClock]

/-- The byte stored as a small number is recovered by the loop's shift and
truncation. -/
theorem installSmallnumByte {width : Nat} [NeZero width] (b : BitVec 8) (good : goodDimindex width) :
    ((smallnum (Int.ofNat b.toNat) : BitVec width) >>> (2 : Nat)).setWidth 8 = b := by
  have hb : b.toNat < 256 := b.isLt
  unfold smallnum
  rw [if_neg (by simp)]
  apply BitVec.eq_of_toNat_eq
  rcases good with rfl | rfl <;> simp <;> omega

/-- A tail call to a known stub. -/
theorem installTailCall {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (loc : Nat) (args : List Nat)
    (xs : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (read : s.getVars args = some xs) (code : sptLookup loc s.code = some (xs.length, prog))
    (clock : s.clock ≠ 0) :
    WordSemStateFiniteExact.evaluate (.call none (some loc) args none) s =
      match WordSemStateFiniteExact.evaluate prog
          (WordSemStateFiniteExact.callEnv xs (sptLookup loc s.stackSize) (WordSemStateFiniteExact.decClock s)) with
      | (res, s) => if wordSemBadFunReturn res then (some .error, s) else (res, s) := by
  simp [WordSemStateFiniteExact.evaluate, read, wordSemBadDestArgs, wordSemFindCode, code,
    wordSemAddRetLoc, clock]

/-- The code-installation loop copies the decoded bytes into the code buffer
and tail-calls the data-installation loop. HOL's universally quantified `v1`
and `s1` occur nowhere in the statement and are omitted. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "InstallCode_code_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem installCode_correct {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (c : Config) (hv1 : Flapjack.Compiler.Backend.DataSem.Value)
    (q1 : List (BitVec 8)) (a1 a2 retVal bptr : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (sp : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (ts : Nat)
    (h : memoryRel c t.be ts refs sp t.store t.memory t.mdomain ((hv1, a1) :: vars) ∧
      sptLookup installCodeLocation t.code = some (4, installCodeStub c) ∧
      sptLookup installDataLocation t.code = some (4, installDataStub c) ∧
      t.store.lookup .bitmapBuffer = some bptr ∧
      DataSem.valueToBytes hv1 = some q1 ∧
      q1.length ≤ t.codeBuffer.spaceLeft ∧ q1.length < t.clock ∧
      t.getVar 0 = some retVal ∧ t.getVar 2 = some a1 ∧ t.getVar 4 = some a2 ∧
      t.getVar 6 = some (.word (t.codeBuffer.position + BitVec.ofNat width t.codeBuffer.buffer.length :
        BitVec width)) ∧
      goodDimindex width) :
    ∃ (lsz smx : Option Nat),
      WordSemStateFiniteExact.evaluate (installCodeStub c) t =
        match WordSemStateFiniteExact.evaluate (installDataStub c)
          { t with
            locals := sptFromList2 [retVal, bptr, a2,
              .word (t.codeBuffer.position + BitVec.ofNat width (t.codeBuffer.buffer.length + q1.length))]
            localsSize := lsz
            clock := t.clock - q1.length - 1
            codeBuffer := { t.codeBuffer with
              buffer := t.codeBuffer.buffer ++ q1
              spaceLeft := t.codeBuffer.spaceLeft - q1.length }
            stackMax := smx } with
        | (res, s) => if wordSemBadFunReturn res then (some .error, s) else (res, s) := by
  induction q1 generalizing t hv1 a1 with
  | nil =>
    obtain ⟨rel, codeL, dataL, bitmap, bytes, space, clock, r0, r2, r4, r6, good⟩ := h
    have list : DataSem.valueToList hv1 = some [] := by
      simpa using (DataSem.valueToBytes_eq_some hv1 []).mp bytes
    obtain ⟨ts0, rfl⟩ := DataSem.valueToList_nil_iff.mp list
    obtain ⟨w, rfl, hw⟩ := memoryRel_blockImp c t.be ts refs sp t.store t.memory t.mdomain ts0 _ [] a1 vars
      ⟨rel, good⟩
    simp only [if_true] at hw
    obtain ⟨_, low, _, _⟩ := hw
    unfold installCodeStub
    rw [installEvalTestOne t 2 w _ _ r2, low, if_neg (by simp)]
    rw [installSeqAssign t 2 _ bptr _ (by simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore, bitmap])]
    rw [installTailCall _ installDataLocation [0, 2, 4, 6]
      [retVal, bptr, a2, .word (t.codeBuffer.position + BitVec.ofNat width t.codeBuffer.buffer.length)] _
      (by simp_all [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar,
            WordSemStateFiniteExact.setVar, installLookupInsert])
      (by simpa [WordSemStateFiniteExact.setVar] using dataL)
      (by simp [WordSemStateFiniteExact.setVar]; omega)]
    refine ⟨sptLookup installDataLocation t.stackSize,
      wordSemOptionMax t.stackMax (wordSemOptionAdd (wordSemStackSize t.stack)
        (sptLookup installDataLocation t.stackSize)), ?_⟩
    simp [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
      WordSemStateFiniteExact.setVar]
  | cons b q1 ih =>
    obtain ⟨rel, codeL, dataL, bitmap, bytes, space, clock, r0, r2, r4, r6, good⟩ := h
    have list := (DataSem.valueToBytes_eq_some hv1 _).mp bytes
    obtain ⟨ts1, tag, tl, rfl, tlList⟩ : ∃ ts1 tag tl, hv1 = .block ts1 tag [.number (Int.ofNat b.toNat), tl] ∧
        DataSem.valueToBytes tl = some q1 := by
      rcases hv1 with _ | _ | ⟨ts1, tag, _ | ⟨hd, _ | ⟨tl, _ | ⟨x, xs⟩⟩⟩⟩ <;>
        simp [DataSem.valueToList] at list
      obtain ⟨-, tlL, rfl⟩ := list
      exact ⟨ts1, tag, tl, rfl, (DataSem.valueToBytes_eq_some tl q1).mpr tlL⟩
    have shift : shiftLength c < width := by
      obtain ⟨_, _, _, _, _, _, heapMem, _⟩ := rel
      exact heapMem.2.2.2.2.2.1
    obtain ⟨w, rfl, hw⟩ := memoryRel_blockImp c t.be ts refs sp t.store t.memory t.mdomain ts1 tag _ a1 vars
      ⟨rel, good⟩
    simp only [reduceCtorEq, if_false] at hw
    obtain ⟨addr, -, high, -, -, addrEq, -⟩ := hw
    obtain ⟨w0, addr0, -, w0Eq, addr0Eq, dom0, rel0⟩ := memoryRel_elAny c t.be ts refs sp t.store t.memory t.mdomain
      ts1 tag _ (.word w) vars 0 (by simp) ⟨rel, good⟩
    cases w0Eq
    rw [addrEq] at addr0Eq
    cases addr0Eq
    obtain ⟨w1, addr1, -, w1Eq, addr1Eq, dom1, rel1⟩ := memoryRel_elAny c t.be ts refs sp t.store t.memory t.mdomain
      ts1 tag _ (.word w) vars 1 (by simp) ⟨rel, good⟩
    cases w1Eq
    rw [addrEq] at addr1Eq
    cases addr1Eq
    have small : smallInt width (Int.ofNat b.toNat) := by
      have hb : b.toNat < 256 := b.isLt
      unfold smallInt
      rcases good with rfl | rfl <;> constructor <;> simp <;> omega
    have m0 := memoryRel_numberImp c t.be ts refs sp t.store t.memory t.mdomain _ _ _ ⟨good, small, rel0⟩
    have relTl := memoryRel_tl c t.be ts refs sp t.store t.memory t.mdomain _ _
      (memoryRel_swap c t.be ts refs sp t.store t.memory t.mdomain _ _ _ rel1)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at m0 relTl
    simp only [BitVec.mul_zero, BitVec.add_zero, BitVec.mul_one] at dom0 m0 dom1 relTl
    have bytesEq : StackRemove.bytesInWord width = wordSemBytesInWord := rfl
    rw [bytesEq] at dom0 m0 dom1 relTl
    unfold installCodeStub
    rw [installEvalTestOne t 2 w _ _ r2, high, if_pos rfl]
    simp only [wordListSeq]
    rw [installSeqAssign t 3 _ (.word addr) _ (getRealAddr_lemma c 2 t w addr ⟨shift, good, r2, addrEq⟩)]
    rw [installSeqAssign _ 2 _ (.word (smallnum (Int.ofNat b.toNat))) _ (by
      simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
        installLookupInsert, theWords, wordOpHOL, wordOp, WordSemStateFiniteExact.memLoad, dom0, m0])]
    rw [installSeqAssign _ 2 _ (.word ((smallnum (Int.ofNat b.toNat) : BitVec width) >>> (2 : Nat))) _ (by
      rw [wordExpShiftVar]
      simp [WordSemStateFiniteExact.setVar, installLookupInsert, SemanticPrimitivesProps.shiftLookup])]
    rw [installSeqCodeBufferWrite _ 6 2 _ _ { t.codeBuffer with
        buffer := t.codeBuffer.buffer ++ [b], spaceLeft := t.codeBuffer.spaceLeft - 1 } _
      (by simpa [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, installLookupInsert] using r6)
      (by simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, installLookupInsert]; rfl)
      (by
        simp only [WordSemStateFiniteExact.setVar, wordSemBufferWrite]
        simp at space
        simp only [Nat.reduceDiv]
        simp
        exact ⟨by omega, installSmallnumByte b good⟩)]
    rw [installSeqAssign _ 6 _ (.word (t.codeBuffer.position + BitVec.ofNat width t.codeBuffer.buffer.length + 1)) _ (by
      have r6' := r6
      simp only [WordSemStateFiniteExact.getVar] at r6'
      simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
        installLookupInsert, theWords, wordOpHOL, wordOp, r6'])]
    have twice : addr + 2#width * wordSemBytesInWord = addr + wordSemBytesInWord + wordSemBytesInWord := by
      rw [BitVec.add_assoc]
      congr 1
      rcases good with rfl | rfl <;> rfl
    rw [installSeqAssign _ 2 _ (t.memory (addr + wordSemBytesInWord + wordSemBytesInWord)) _ (by
      simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
        installLookupInsert, theWords, wordOpHOL, wordOp, WordSemStateFiniteExact.memLoad]
      rw [twice]; exact ⟨dom1, rfl⟩)]
    have r0' := r0
    have r4' := r4
    simp only [WordSemStateFiniteExact.getVar] at r0' r4'
    simp at space clock
    rw [installTailCall _ installCodeLocation [0, 2, 4, 6]
      [retVal, t.memory (addr + wordSemBytesInWord + wordSemBytesInWord), a2,
        .word (t.codeBuffer.position + BitVec.ofNat width t.codeBuffer.buffer.length + 1)] _
      (by simp [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar,
            WordSemStateFiniteExact.setVar, installLookupInsert, r0', r4'])
      (by simpa [WordSemStateFiniteExact.setVar] using codeL)
      (by simp [WordSemStateFiniteExact.setVar]; omega)]
    let m1 := t.memory (addr + wordSemBytesInWord + wordSemBytesInWord)
    let t88 : WordSemStateFiniteExact width C F := { t with
      locals := sptFromList2 [retVal, m1, a2,
        .word (t.codeBuffer.position + BitVec.ofNat width t.codeBuffer.buffer.length + 1)]
      localsSize := sptLookup installCodeLocation t.stackSize
      stackMax := wordSemOptionMax t.stackMax
        (wordSemOptionAdd (wordSemStackSize t.stack) (sptLookup installCodeLocation t.stackSize))
      codeBuffer := { t.codeBuffer with
        buffer := t.codeBuffer.buffer ++ [b], spaceLeft := t.codeBuffer.spaceLeft - 1 }
      clock := t.clock - 1 }
    have v6 : t88.codeBuffer.position + BitVec.ofNat width t88.codeBuffer.buffer.length =
        t.codeBuffer.position + BitVec.ofNat width t.codeBuffer.buffer.length + 1 := by
      simp [t88, BitVec.ofNat_add, BitVec.add_assoc]
    obtain ⟨lsz, smx, ihEq⟩ := ih t88 tl m1 ⟨relTl, codeL, dataL, bitmap,
      tlList, by simp [t88]; omega, by simp [t88]; omega,
      by simp [t88, WordSemStateFiniteExact.getVar, WordToStackProofs.fromList2Lookup],
      by simp [t88, m1, WordSemStateFiniteExact.getVar, WordToStackProofs.fromList2Lookup],
      by simp [t88, WordSemStateFiniteExact.getVar, WordToStackProofs.fromList2Lookup],
      by rw [v6]; simp [t88, WordSemStateFiniteExact.getVar, WordToStackProofs.fromList2Lookup],
      good⟩
    have step : ∀ s, s = t88 → WordSemStateFiniteExact.evaluate (installCodeStub c) s = _ :=
      fun s h => h ▸ ihEq
    rw [step]
    · refine ⟨lsz, smx, ?_⟩
      generalize hp : WordSemStateFiniteExact.evaluate (installDataStub (width := width) c) (_ : WordSemStateFiniteExact width C F) = p
      generalize hq : WordSemStateFiniteExact.evaluate (installDataStub (width := width) c) (_ : WordSemStateFiniteExact width C F) = q
      have pq : p = q := by
        rw [← hp, ← hq]
        congr 1
        simp [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
          WordSemStateFiniteExact.setVar, List.append_assoc, Nat.sub_sub, Nat.add_comm, Nat.add_left_comm,
          BitVec.ofNat_add, BitVec.add_assoc]
      subst pq
      obtain ⟨res, s⟩ := p
      by_cases h : wordSemBadFunReturn res = true
      · simp only [h, if_true]
        simp [wordSemBadFunReturn]
      · simp only [h, if_false, Bool.false_eq_true]
    · rfl

/-- The data-installation loop copies the decoded words into the data buffer
and tail-calls the installation stub. HOL's universally quantified `v1` and
`s1` occur nowhere in the statement and are omitted. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "InstallData_code_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem installData_correct {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (c : Config) (hv2 : Flapjack.Compiler.Backend.DataSem.Value)
    (q2 : List (BitVec 64)) (a1 a2 retVal : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (sp : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (ts : Nat)
    (h : memoryRel c t.be ts refs sp t.store t.memory t.mdomain ((hv2, a2) :: vars) ∧
      sptLookup installDataLocation t.code = some (4, installDataStub c) ∧
      sptLookup installLocation t.code = some (3, installCode c) ∧
      DataSem.valueToWords hv2 = some q2 ∧
      q2.length ≤ t.dataBuffer.spaceLeft ∧ q2.length < t.clock ∧
      t.getVar 0 = some retVal ∧
      t.getVar 2 = some (.word (t.dataBuffer.position +
        wordSemBytesInWord * BitVec.ofNat width t.dataBuffer.buffer.length : BitVec width)) ∧
      t.getVar 4 = some a2 ∧ t.getVar 6 = some a1 ∧
      goodDimindex width) :
    ∃ (smx lsz : Option Nat),
      WordSemStateFiniteExact.evaluate (installDataStub c) t =
        match WordSemStateFiniteExact.evaluate (installCode c)
          { t with
            locals := sptFromList2 [retVal,
              .word (t.dataBuffer.position +
                wordSemBytesInWord * BitVec.ofNat width t.dataBuffer.buffer.length +
                wordSemBytesInWord * BitVec.ofNat width q2.length), a1]
            clock := t.clock - q2.length - 1
            dataBuffer := { t.dataBuffer with
              buffer := t.dataBuffer.buffer ++ q2.map w2wUpper
              spaceLeft := t.dataBuffer.spaceLeft - q2.length }
            localsSize := lsz
            stackMax := smx } with
        | (res, s) => if wordSemBadFunReturn res then (some .error, s) else (res, s) := by
  induction q2 generalizing t hv2 a2 with
  | nil =>
    obtain ⟨rel, dataL, installL, words, space, clock, r0, r2, r4, r6, good⟩ := h
    have list : DataSem.valueToList hv2 = some [] := by
      simpa using (DataSem.valueToWords_eq_some hv2 []).mp words
    obtain ⟨ts0, rfl⟩ := DataSem.valueToList_nil_iff.mp list
    obtain ⟨w, rfl, hw⟩ := memoryRel_blockImp c t.be ts refs sp t.store t.memory t.mdomain ts0 _ [] a2 vars
      ⟨rel, good⟩
    simp only [if_true] at hw
    obtain ⟨_, low, _, _⟩ := hw
    unfold installDataStub
    rw [installEvalTestOne t 4 w _ _ r4, low, if_neg (by simp)]
    have r0' := r0
    have r2' := r2
    have r6' := r6
    simp only [WordSemStateFiniteExact.getVar] at r0' r2' r6'
    rw [installTailCall _ installLocation [0, 2, 6]
      [retVal, .word (t.dataBuffer.position +
        wordSemBytesInWord * BitVec.ofNat width t.dataBuffer.buffer.length), a1] _
      (by simp [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, r0', r2', r6'])
      (by simpa using installL)
      (by simp at clock; omega)]
    refine ⟨wordSemOptionMax t.stackMax (wordSemOptionAdd (wordSemStackSize t.stack)
        (sptLookup installLocation t.stackSize)), sptLookup installLocation t.stackSize, ?_⟩
    simp [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock]
  | cons v q2 ih =>
    obtain ⟨rel, dataL, installL, words, space, clock, r0, r2, r4, r6, good⟩ := h
    have list := (DataSem.valueToWords_eq_some hv2 _).mp words
    obtain ⟨ts1, tag, tl, rfl, tlList⟩ : ∃ ts1 tag tl, hv2 = .block ts1 tag [.word64 v, tl] ∧
        DataSem.valueToWords tl = some q2 := by
      rcases hv2 with _ | _ | ⟨ts1, tag, _ | ⟨hd, _ | ⟨tl, _ | ⟨x, xs⟩⟩⟩⟩ <;>
        simp [DataSem.valueToList] at list
      obtain ⟨-, tlL, rfl⟩ := list
      exact ⟨ts1, tag, tl, rfl, (DataSem.valueToWords_eq_some tl q2).mpr tlL⟩
    have shift : shiftLength c < width := by
      obtain ⟨_, _, _, _, _, _, heapMem, _⟩ := rel
      exact heapMem.2.2.2.2.2.1
    obtain ⟨w, rfl, hw⟩ := memoryRel_blockImp c t.be ts refs sp t.store t.memory t.mdomain ts1 tag _ a2 vars
      ⟨rel, good⟩
    simp only [reduceCtorEq, if_false] at hw
    obtain ⟨addr, -, high, -, -, addrEq, -⟩ := hw
    obtain ⟨w0, addr0, -, w0Eq, addr0Eq, dom0, rel0⟩ := memoryRel_elAny c t.be ts refs sp t.store t.memory t.mdomain
      ts1 tag _ (.word w) vars 0 (by simp) ⟨rel, good⟩
    cases w0Eq
    rw [addrEq] at addr0Eq
    cases addr0Eq
    obtain ⟨w1, addr1, -, w1Eq, addr1Eq, dom1, rel1⟩ := memoryRel_elAny c t.be ts refs sp t.store t.memory t.mdomain
      ts1 tag _ (.word w) vars 1 (by simp) ⟨rel, good⟩
    cases w1Eq
    rw [addrEq] at addr1Eq
    cases addr1Eq
    have relTl := memoryRel_tl c t.be ts refs sp t.store t.memory t.mdomain _ _
      (memoryRel_swap c t.be ts refs sp t.store t.memory t.mdomain _ _ _ rel1)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at rel0 relTl
    simp only [BitVec.mul_zero, BitVec.add_zero, BitVec.mul_one] at dom0 rel0 dom1 relTl
    have bytesEq : StackRemove.bytesInWord width = wordSemBytesInWord := rfl
    rw [bytesEq] at dom0 rel0 dom1 relTl
    obtain ⟨ptr, address, header, m0, realEq, -, -, -, -, -, domA, hv⟩ :=
      memoryRel_word64Imp c t.be ts refs sp t.store t.memory t.mdomain v _ _ ⟨rel0, good⟩
    rw [bytesEq] at domA hv
    have mA : t.memory (address + wordSemBytesInWord) = .word (w2wUpper v) := by
      rcases good with hw | hw <;> subst width <;> simp [w2wUpper] at hv ⊢ <;> exact hv.1
    have r0' := r0
    have r2' := r2
    have r6' := r6
    simp only [WordSemStateFiniteExact.getVar] at r0' r2' r6'
    simp at space clock
    unfold installDataStub
    rw [installEvalTestOne t 4 w _ _ r4, high, if_pos rfl]
    simp only [wordListSeq]
    rw [installSeqAssign t 3 _ (.word addr) _ (getRealAddr_lemma c 4 t w addr ⟨shift, good, r4, addrEq⟩)]
    rw [installSeqAssign _ 4 _ (.word (getAddr c ptr (.word 0))) _ (by
      simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
        installLookupInsert, theWords, wordOpHOL, wordOp, WordSemStateFiniteExact.memLoad, dom0, m0])]
    rw [installSeqAssign _ 4 _ (.word address) _ (getRealAddr_lemma c 4 _ (getAddr c ptr (.word 0)) address
      ⟨shift, good, by simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, installLookupInsert],
        by simpa [WordSemStateFiniteExact.setVar] using realEq⟩)]
    rw [installSeqAssign _ 4 _ (.word (w2wUpper v)) _ (by
      simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
        installLookupInsert, theWords, wordOpHOL, wordOp, WordSemStateFiniteExact.memLoad, domA, mA])]
    rw [installSeqDataBufferWrite _ 2 4
      (t.dataBuffer.position + wordSemBytesInWord * BitVec.ofNat width t.dataBuffer.buffer.length)
      (w2wUpper v) { t.dataBuffer with
        buffer := t.dataBuffer.buffer ++ [w2wUpper v], spaceLeft := t.dataBuffer.spaceLeft - 1 } _
      (by simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, installLookupInsert, r2'])
      (by simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, installLookupInsert])
      (by
        simp only [WordSemStateFiniteExact.setVar, wordSemBufferWrite]
        exact if_pos ⟨rfl, by omega⟩)]
    rw [installSeqAssign _ 2 _ (.word (t.dataBuffer.position +
        wordSemBytesInWord * BitVec.ofNat width t.dataBuffer.buffer.length + wordSemBytesInWord)) _ (by
      simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
        installLookupInsert, theWords, wordOpHOL, wordOp, r2'])]
    have twice : addr + 2#width * wordSemBytesInWord = addr + wordSemBytesInWord + wordSemBytesInWord := by
      rw [BitVec.add_assoc]
      congr 1
      rcases good with rfl | rfl <;> rfl
    rw [installSeqAssign _ 4 _ (t.memory (addr + wordSemBytesInWord + wordSemBytesInWord)) _ (by
      simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
        installLookupInsert, theWords, wordOpHOL, wordOp, WordSemStateFiniteExact.memLoad]
      rw [twice]; exact ⟨dom1, rfl⟩)]
    rw [installTailCall _ installDataLocation [0, 2, 4, 6]
      [retVal, .word (t.dataBuffer.position +
        wordSemBytesInWord * BitVec.ofNat width t.dataBuffer.buffer.length + wordSemBytesInWord),
        t.memory (addr + wordSemBytesInWord + wordSemBytesInWord), a1] _
      (by simp [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar,
            WordSemStateFiniteExact.setVar, installLookupInsert, r0', r6'])
      (by simpa [WordSemStateFiniteExact.setVar] using dataL)
      (by simp [WordSemStateFiniteExact.setVar]; omega)]
    let m1 := t.memory (addr + wordSemBytesInWord + wordSemBytesInWord)
    let t88 : WordSemStateFiniteExact width C F := { t with
      locals := sptFromList2 [retVal, .word (t.dataBuffer.position +
        wordSemBytesInWord * BitVec.ofNat width t.dataBuffer.buffer.length + wordSemBytesInWord), m1, a1]
      localsSize := sptLookup installDataLocation t.stackSize
      stackMax := wordSemOptionMax t.stackMax
        (wordSemOptionAdd (wordSemStackSize t.stack) (sptLookup installDataLocation t.stackSize))
      dataBuffer := { t.dataBuffer with
        buffer := t.dataBuffer.buffer ++ [w2wUpper v], spaceLeft := t.dataBuffer.spaceLeft - 1 }
      clock := t.clock - 1 }
    have v2 : t88.dataBuffer.position + wordSemBytesInWord * BitVec.ofNat width t88.dataBuffer.buffer.length =
        t.dataBuffer.position + wordSemBytesInWord * BitVec.ofNat width t.dataBuffer.buffer.length +
          wordSemBytesInWord := by
      simp [t88, BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]
    obtain ⟨smx, lsz, ihEq⟩ := ih t88 tl m1 ⟨relTl, dataL, installL,
      tlList, by simp [t88]; omega, by simp [t88]; omega,
      by simp [t88, WordSemStateFiniteExact.getVar, WordToStackProofs.fromList2Lookup],
      by rw [v2]; simp [t88, WordSemStateFiniteExact.getVar, WordToStackProofs.fromList2Lookup],
      by simp [t88, m1, WordSemStateFiniteExact.getVar, WordToStackProofs.fromList2Lookup],
      by simp [t88, WordSemStateFiniteExact.getVar, WordToStackProofs.fromList2Lookup],
      good⟩
    have step : ∀ s, s = t88 → WordSemStateFiniteExact.evaluate (installDataStub c) s = _ :=
      fun s h => h ▸ ihEq
    rw [step]
    · refine ⟨smx, lsz, ?_⟩
      generalize hp : WordSemStateFiniteExact.evaluate (installCode (width := width) c)
        (_ : WordSemStateFiniteExact width C F) = p
      generalize hq : WordSemStateFiniteExact.evaluate (installCode (width := width) c)
        (_ : WordSemStateFiniteExact width C F) = q
      have pq : p = q := by
        rw [← hp, ← hq]
        congr 1
        simp [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
          WordSemStateFiniteExact.setVar, List.append_assoc, Nat.sub_sub,
          BitVec.ofNat_add, BitVec.add_assoc, BitVec.mul_add, add_comm]
      subst pq
      obtain ⟨res, s⟩ := p
      by_cases h : wordSemBadFunReturn res = true
      · simp only [h, if_true]
        simp [wordSemBadFunReturn]
      · simp only [h, if_false, Bool.false_eq_true]
    · rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
