module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Compare1
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BignumCompare
@[expose] public section

/-! Correctness of the data-to-word integer comparison runtime stub. -/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataSem
open Classical
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Bit-zero testing for immediate values, used in the HOL comparison proof. -/
private theorem lowBitZero {width : Nat} (w : BitVec width) (low : w.getLsbD 0 = false) :
    w &&& 1 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (1 : BitVec width) = BitVec.ofNat width 1 from rfl]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat]
  cases i with
  | zero => simp [low]
  | succ i => simp [Nat.testBit_succ]

/-- Execute an assignment before its continuation, as in the HOL evaluator proof. -/
private theorem seqAssign {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (key : Nat) (expr : WordLangExpHOL (BitVec width))
    (v : WordLocW width) (tail : WordLangProgHOL (BitVec width))
    (read : s.wordExp expr = some v) :
    WordSemStateFiniteExact.evaluate (.seq (.assign key expr) tail) s =
      WordSemStateFiniteExact.evaluate tail (s.setVar key v) := by
  simp [WordSemStateFiniteExact.evaluate, read, WordSemStateFiniteExact.fixClock,
    WordSemStateFiniteExact.setVar]

/-- Reverse the immediate-versus-heap comparison result in the second HOL branch. -/
private theorem reverseSmallLarge {width : Nat} [NeZero width] (i1 i2 : Int) (header : BitVec width)
    (good : goodDimindex width) (different : i2 ≠ i1)
    (result : wordCmpRes (width := width) i2 i1 = if header &&& 16 = 0 then 0 else 2) :
    wordCmpRes (width := width) i1 i2 = if header &&& 16 = 0 then 2 else 0 := by
  have neq : i1 ≠ i2 := Ne.symm different
  rcases good with hw | hw <;> subst width <;>
    by_cases hi : header &&& 16 = 0 <;> by_cases lt : i1 < i2 <;> by_cases gt : i2 < i1 <;>
    simp [wordCmpRes, neq, different, lt, gt] at result ⊢ <;> omega

namespace CompareCodeWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end CompareCodeWitness

/-- The comparison stub returns the HOL integer comparison result within its stack bound. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "Compare_code_thm"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store, store])
  (words_as_type_indexed_bitvec)]
theorem compareCode_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (be : Bool) (ts : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (i1 i2 : Int) (v1 v2 : BitVec width) (vars : List (Value × WordLocW width))
    (t : WordSemStateFiniteExact width C F) (l1 l2 : Nat)
    (h : memoryRel conf be ts refs space store memory domain ((.number i1,.word v1)::(.number i2,.word v2)::vars) ∧
      domain = t.mdomain ∧ memory = t.memory ∧ store = t.store ∧
      (v1.getLsbD 0 = false → v2.getLsbD 0 = true) ∧ shiftLength conf < width ∧
      sptLookup compare1Location t.code = some (4,compare1Code) ∧
      t.getVar 0 = some (.loc l1 l2) ∧ t.getVar 2 = some (.word v1) ∧ t.getVar 4 = some (.word v2) ∧
      2 ^ width < t.clock ∧ conf.lenSize ≠ 0 ∧ conf.lenSize < width ∧ goodDimindex width) :
    ∃ ck smx, WordSemStateFiniteExact.evaluate (compareCode conf) t =
      (some (.result (.loc l1 l2) [.word (wordCmpRes i1 i2)]),
        {t with clock := ck, locals := .ln, localsSize := some 0, stackMax := smx}) ∧
      optionLe smx (Option.map₂ max t.stackMax
        (Option.map₂ (· + ·) (wordSemStackSize t.stack) (sptLookup compare1Location t.stackSize))) := by
  obtain ⟨rel, dom, mem, storeEq, bitImp, shift, code, r0, r2, r4, clock, lenNe, lenLt, good⟩ := h
  obtain ⟨u1, u2, eq1, eq2, cmp⟩ := memoryRel_numberCmp conf be ts refs space store memory domain
    i1 i2 (.word v1) (.word v2) vars ⟨rel, good⟩
  have u1eq : u1 = v1 := (WordLocW.word.inj eq1).symm
  have u2eq : u2 = v2 := (WordLocW.word.inj eq2).symm
  subst u1
  subst u2
  by_cases low1 : v1.getLsbD 0 = false
  · have high2 : v2.getLsbD 0 = true := bitImp low1
    simp only [low1, high2, Bool.true_eq_false, Bool.false_eq_true, true_and, false_and, if_true, if_false] at cmp
    obtain ⟨different, address, header, addr, head, present, result⟩ := cmp
    have regAddr : t.wordExp (realAddr conf 4) = some (.word address) :=
      Bignum.getRealAddr_lemma conf 4 t v2 address ⟨shift, good, r4, by simpa [storeEq] using addr⟩
    have valid : t.mdomain address = true := by simpa [dom] using present
    have load : t.memory address = .word header := by simpa [mem] using head
    have mask := lowBitZero v1 low1
    refine ⟨t.clock, t.stackMax, ?_, ?_⟩
    · have test : wordSemWordCmp .test (.word v1) (.word (1 : BitVec width)) = some true := by
        simp only [wordSemWordCmp, Encoders.Asm.wordCmpHOL, Option.some.injEq]
        change (v1 &&& (1 : BitVec width) == 0) = true
        exact beq_iff_eq.mpr mask
      have loaded : t.wordExp (.load (realAddr conf 4)) = some (.word header) := by
        simp only [WordSemStateFiniteExact.wordExp, regAddr, WordSemStateFiniteExact.memLoad, valid, if_true, load]
      rw [compareCode, WordSemStateFiniteExact.evaluate, r2]
      simp only [WordSemStateFiniteExact.getVarImm, test, wordListSeq]
      rw [seqAssign t 1 _ (.word header) _ loaded]
      let s1 := t.setVar 1 (.word header)
      have read1 : s1.getVar 1 = some (.word header) := by
        simp [s1, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
      have r0lookup : sptLookup 0 t.locals = some (.loc l1 l2) := by simpa [WordSemStateFiniteExact.getVar] using r0
      rw [WordSemStateFiniteExact.evaluate, read1]
      simp only [WordSemStateFiniteExact.getVarImm]
      rw [result]
      by_cases isZero : header &&& (16 : BitVec width) = 0
      · rw [if_pos isZero]
        have ht : wordSemWordCmp .test (.word header) (.word (16 : BitVec width)) = some true := by
          simp only [wordSemWordCmp, Encoders.Asm.wordCmpHOL, Option.some.injEq]
          change (header &&& (16 : BitVec width) == 0) = true
          exact beq_iff_eq.mpr isZero
        rw [ht]
        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
          WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
          WordSemStateFiniteExact.fixClock, WordSemStateFiniteExact.flushState,
          sptLookup_sptInsert_ne, sptLookup_sptInsert_same, r0lookup]
      · rw [if_neg isZero]
        have ht : wordSemWordCmp .test (.word header) (.word (16 : BitVec width)) = some false := by
          simp only [wordSemWordCmp, Encoders.Asm.wordCmpHOL, Option.some.injEq]
          change (header &&& (16 : BitVec width) == 0) = false
          exact beq_eq_false_iff_ne.mpr isZero
        rw [ht]
        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
          WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
          WordSemStateFiniteExact.fixClock, WordSemStateFiniteExact.flushState,
          sptLookup_sptInsert_ne, sptLookup_sptInsert_same, r0lookup]
    · exact (optionLe_max_right _ _ _).2 (Or.inl (optionLe_refl _))
  · have high1 : v1.getLsbD 0 = true := by cases bit : v1.getLsbD 0 <;> simp_all
    by_cases low2 : v2.getLsbD 0 = false
    · have swapped := memoryRel_rearrange conf be ts refs space store memory domain
        ((.number i1,.word v1)::(.number i2,.word v2)::vars)
        ((.number i2,.word v2)::(.number i1,.word v1)::vars) (by
          intro pair member; simp only [List.mem_cons] at member ⊢; tauto) rel
      obtain ⟨w2, w1, weq2, weq1, cmpSwap⟩ := memoryRel_numberCmp conf be ts refs space store memory domain
        i2 i1 (.word v2) (.word v1) vars ⟨swapped, good⟩
      have w2eq : w2 = v2 := (WordLocW.word.inj weq2).symm
      have w1eq : w1 = v1 := (WordLocW.word.inj weq1).symm
      subst w2
      subst w1
      simp only [low2, high1, Bool.true_eq_false, Bool.false_eq_true, true_and, false_and, if_true, if_false] at cmpSwap
      obtain ⟨different, address, header, addr, head, present, result⟩ := cmpSwap
      have inverse : wordCmpRes (width := width) i1 i2 = if header &&& 16 = 0 then 2 else 0 :=
        reverseSmallLarge i1 i2 header good different result
      have regAddr : t.wordExp (realAddr conf 2) = some (.word address) :=
        Bignum.getRealAddr_lemma conf 2 t v1 address ⟨shift, good, r2, by simpa [storeEq] using addr⟩
      have valid : t.mdomain address = true := by simpa [dom] using present
      have load : t.memory address = .word header := by simpa [mem] using head
      have mask : v1 &&& (1 : BitVec width) ≠ 0 := by
        intro eq
        have bits := congrArg (fun v : BitVec width => v.getLsbD 0) eq
        have pos : 0 < width := NeZero.pos width
        simp [pos] at bits
        rw [BitVec.getLsbD_eq_getElem pos] at high1
        simp_all
      have test1 : wordSemWordCmp .test (.word v1) (.word (1 : BitVec width)) = some false := by
        simp only [wordSemWordCmp, Encoders.Asm.wordCmpHOL, Option.some.injEq]
        change (v1 &&& (1 : BitVec width) == 0) = false
        exact beq_eq_false_iff_ne.mpr mask
      have test2 : wordSemWordCmp .test (.word v2) (.word (1 : BitVec width)) = some true := by
        simp only [wordSemWordCmp, Encoders.Asm.wordCmpHOL, Option.some.injEq]
        change (v2 &&& (1 : BitVec width) == 0) = true
        exact beq_iff_eq.mpr (lowBitZero v2 low2)
      have loaded : t.wordExp (.load (realAddr conf 2)) = some (.word header) := by
        simp only [WordSemStateFiniteExact.wordExp, regAddr, WordSemStateFiniteExact.memLoad, valid, if_true, load]
      refine ⟨t.clock, t.stackMax, ?_, ?_⟩
      · rw [compareCode, WordSemStateFiniteExact.evaluate, r2]
        simp only [WordSemStateFiniteExact.getVarImm, test1]
        rw [WordSemStateFiniteExact.evaluate, r4]
        simp only [WordSemStateFiniteExact.getVarImm, test2, wordListSeq]
        rw [seqAssign t 1 _ (.word header) _ loaded]
        let s1 := t.setVar 1 (.word header)
        have read1 : s1.getVar 1 = some (.word header) := by
          simp [s1, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
        have r0lookup : sptLookup 0 t.locals = some (.loc l1 l2) := by simpa [WordSemStateFiniteExact.getVar] using r0
        rw [WordSemStateFiniteExact.evaluate, read1]
        simp only [WordSemStateFiniteExact.getVarImm]
        rw [inverse]
        by_cases isZero : header &&& (16 : BitVec width) = 0
        · rw [if_pos isZero]
          have ht : wordSemWordCmp .test (.word header) (.word (16 : BitVec width)) = some true := by
            simp only [wordSemWordCmp, Encoders.Asm.wordCmpHOL, Option.some.injEq]
            change (header &&& (16 : BitVec width) == 0) = true
            exact beq_iff_eq.mpr isZero
          rw [ht]
          simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
            WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
            WordSemStateFiniteExact.fixClock, WordSemStateFiniteExact.flushState,
            sptLookup_sptInsert_ne, sptLookup_sptInsert_same, r0lookup]
        · rw [if_neg isZero]
          have ht : wordSemWordCmp .test (.word header) (.word (16 : BitVec width)) = some false := by
            simp only [wordSemWordCmp, Encoders.Asm.wordCmpHOL, Option.some.injEq]
            change (header &&& (16 : BitVec width) == 0) = false
            exact beq_eq_false_iff_ne.mpr isZero
          rw [ht]
          simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
            WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
            WordSemStateFiniteExact.fixClock, WordSemStateFiniteExact.flushState,
            sptLookup_sptInsert_ne, sptLookup_sptInsert_same, r0lookup]
      · exact (optionLe_max_right _ _ _).2 (Or.inl (optionLe_refl _))
    · have high2 : v2.getLsbD 0 = true := by cases bit : v2.getLsbD 0 <;> simp_all
      simp only [high1, high2, Bool.true_eq_false, false_and, and_self, if_false, if_true] at cmp
      obtain ⟨a1, x1, a2, x2, addr1, mem1, dm1, addr2, mem2, dm2, cmpBody⟩ := cmp
      have real1 : t.wordExp (realAddr conf 2) = some (.word a1) :=
        Bignum.getRealAddr_lemma conf 2 t v1 a1 ⟨shift, good, r2, by simpa [storeEq] using addr1⟩
      have real2 : t.wordExp (realAddr conf 4) = some (.word a2) :=
        Bignum.getRealAddr_lemma conf 4 t v2 a2 ⟨shift, good, r4, by simpa [storeEq] using addr2⟩
      have valid1 : t.mdomain a1 = true := by simpa [dom] using dm1
      have valid2 : t.mdomain a2 = true := by simpa [dom] using dm2
      have load1 : t.memory a1 = .word x1 := by simpa [mem] using mem1
      have load2 : t.memory a2 = .word x2 := by simpa [mem] using mem2
      have testHigh : ∀ v : BitVec width, v.getLsbD 0 = true →
          wordSemWordCmp .test (.word v) (.word (1 : BitVec width)) = some false := by
        intro v high
        have mask : v &&& (1 : BitVec width) ≠ 0 := by
          intro eq
          have bits := congrArg (fun x : BitVec width => x.getLsbD 0) eq
          have pos : 0 < width := NeZero.pos width
          simp [pos] at bits
          rw [BitVec.getLsbD_eq_getElem pos] at high
          simp_all
        simp only [wordSemWordCmp, Encoders.Asm.wordCmpHOL, Option.some.injEq]
        change (v &&& (1 : BitVec width) == 0) = false
        exact beq_eq_false_iff_ne.mpr mask
      let s11 := t.setVar 11 (.word a1)
      have read11 : s11.wordExp (.load (.var 11)) = some (.word x1) := by
        simp [s11, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.memLoad,
          sptLookup_sptInsert_same, valid1, load1]
      let s1 := s11.setVar 1 (.word x1)
      have readReal2 : s1.wordExp (realAddr conf 4) = some (.word a2) := by
        have preserve := (wordExp_realAddr_insert conf t 4 1 11 (.word x1) (.word a1)).2
          (by simp)
        simpa [s1, s11, WordSemStateFiniteExact.setVar] using preserve.trans real2
      let s13 := s1.setVar 13 (.word a2)
      have read13 : s13.wordExp (.load (.var 13)) = some (.word x2) := by
        simp [s13, s1, s11, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.memLoad,
          sptLookup_sptInsert_same, valid2, load2]
      have shiftLt : width - conf.lenSize < width := by omega
      have shiftMod : (width - conf.lenSize) % 2 ^ width = width - conf.lenSize := by
        apply Nat.mod_eq_of_lt
        rcases good with h | h <;> subst width <;> norm_num at * <;> omega
      let s3 := s13.setVar 3 (.word x2)
      have readShift1 : s3.wordExp (shiftN .lsr (.var 1) (width - conf.lenSize)) =
          some (.word (WordGcFunctions.decodeLength conf x1)) := by
        simp [shiftN, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, s3, s13, s1, s11, sptLookup_sptInsert_ne,
          sptLookup_sptInsert_same, WordGcFunctions.decodeLength,
          wordShiftHOL, shiftMod, show ¬ width ≤ width - conf.lenSize by omega]
      let s6 := s3.setVar 6 (.word (WordGcFunctions.decodeLength conf x1))
      have readShift2 : s6.wordExp (shiftN .lsr (.var 3) (width - conf.lenSize)) =
          some (.word (WordGcFunctions.decodeLength conf x2)) := by
        simp [shiftN, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, s6, s3, s13, s1, s11, sptLookup_sptInsert_ne,
          sptLookup_sptInsert_same, WordGcFunctions.decodeLength,
          wordShiftHOL, shiftMod, show ¬ width ≤ width - conf.lenSize by omega]
      let s8 := s6.setVar 8 (.word (WordGcFunctions.decodeLength conf x2))
      have s8get1 : s8.getVar 1 = some (.word x1) := by
        simp [s8, s6, s3, s13, s1, s11, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
      have s8get3 : s8.getVar 3 = some (.word x2) := by
        simp [s8, s6, s3, s13, s1, s11, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
      have s8get6 : s8.getVar 6 = some (.word (WordGcFunctions.decodeLength conf x1)) := by
        simp [s8, s6, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
          sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
      have s8get8 : s8.getVar 8 = some (.word (WordGcFunctions.decodeLength conf x2)) := by
        simp [s8, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
      have s8get0 : s8.getVar 0 = some (.loc l1 l2) := by
        simpa [s8, s6, s3, s13, s1, s11, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne] using r0
      have sl1 : sptLookup 1 s8.locals = some (.word x1) := by simpa [WordSemStateFiniteExact.getVar] using s8get1
      have sl3 : sptLookup 3 s8.locals = some (.word x2) := by simpa [WordSemStateFiniteExact.getVar] using s8get3
      have sl6 : sptLookup 6 s8.locals = some (.word (WordGcFunctions.decodeLength conf x1)) := by simpa [WordSemStateFiniteExact.getVar] using s8get6
      have sl8 : sptLookup 8 s8.locals = some (.word (WordGcFunctions.decodeLength conf x2)) := by simpa [WordSemStateFiniteExact.getVar] using s8get8
      have sl0 : sptLookup 0 s8.locals = some (.loc l1 l2) := by simpa [WordSemStateFiniteExact.getVar] using s8get0
      let result (n : Nat) : WordLangProgHOL (BitVec width) :=
        .seq (.assign 2 (.const (BitVec.ofNat width n))) (.return 0 [2])
      let tail : WordLangProgHOL (BitVec width) :=
        .ite .equal 1 (.reg 3)
          (wordListSeq [.assign 2 (.op .add [.var 11, shiftN .lsl (.var 6) (wordShiftAmount width)]),
            .assign 4 (.op .add [.var 13, shiftN .lsl (.var 6) (wordShiftAmount width)]),
            .ite .test 1 (.imm 16) (.call none (some compare1Location) [0, 6, 2, 4] none)
              (.call none (some compare1Location) [0, 6, 4, 2] none)])
          (.ite .test 1 (.imm 16)
            (.ite .test 3 (.imm 16) (.ite .lower 6 (.reg 8) (result 0) (result 2)) (result 2))
            (.ite .test 3 (.imm 16) (result 0) (.ite .lower 6 (.reg 8) (result 2) (result 0))))
      have setupEval : WordSemStateFiniteExact.evaluate (compareCode conf) t =
          WordSemStateFiniteExact.evaluate tail s8 := by
        rw [compareCode, WordSemStateFiniteExact.evaluate, r2]
        simp only [WordSemStateFiniteExact.getVarImm, testHigh v1 high1]
        rw [WordSemStateFiniteExact.evaluate, r4]
        simp only [WordSemStateFiniteExact.getVarImm, testHigh v2 high2, wordListSeq]
        rw [seqAssign t 11 _ (.word a1) _ real1]
        change WordSemStateFiniteExact.evaluate _ s11 = _
        rw [seqAssign s11 1 _ (.word x1) _ read11]
        change WordSemStateFiniteExact.evaluate _ s1 = _
        rw [seqAssign s1 13 _ (.word a2) _ readReal2]
        change WordSemStateFiniteExact.evaluate _ s13 = _
        rw [seqAssign s13 3 _ (.word x2) _ read13]
        change WordSemStateFiniteExact.evaluate _ s3 = _
        rw [seqAssign s3 6 _ (.word (WordGcFunctions.decodeLength conf x1)) _ readShift1]
        change WordSemStateFiniteExact.evaluate _ s6 = _
        rw [seqAssign s6 8 _ (.word (WordGcFunctions.decodeLength conf x2)) _ readShift2]
        rfl
      by_cases headers : x1 = x2
      · subst x2
        let count := WordGcFunctions.decodeLength conf x1
        let left := (if x1 &&& 16 = 0 then a1 else a2) + StackRemove.bytesInWord width * count
        let right := (if x1 &&& 16 = 0 then a2 else a1) + StackRemove.bytesInWord width * count
        let entry := WordSemStateFiniteExact.callEnv
          [.loc l1 l2, .word count, .word left, .word right]
          (sptLookup compare1Location t.stackSize) (WordSemStateFiniteExact.decClock t)
        have loop : wordCmpLoop count left right domain memory = some (wordCmpRes i1 i2) := by
          simpa [count, left, right] using cmpBody
        have countBound : count.toNat ≤ entry.clock := by
          change count.toNat ≤ t.clock - 1
          have bound := count.isLt
          omega
        have entry0 : entry.getVar 0 = some (.loc l1 l2) := by
          simp [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar,
            sptFromList2, sptLookup_sptInsert_ne, sptLookup]
        have entry2 : entry.getVar 2 = some (.word count) := by
          simp [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar,
            sptFromList2, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
        have entry4 : entry.getVar 4 = some (.word left) := by
          simp [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar,
            sptFromList2, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
        have entry6 : entry.getVar 6 = some (.word right) := by
          simp [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar,
            sptFromList2, sptLookup_sptInsert_same]
        obtain ⟨ck, smx, eval, stackBound, clockBound⟩ := compare1Code_correct
          count left right domain memory (wordCmpRes i1 i2) entry l1 l2 loop
          (by simpa [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock] using dom)
          (by simpa [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock] using mem)
          (by simpa [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock] using code)
          (by simp [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock])
          entry0 entry2 entry4 entry6 countBound
        refine ⟨ck, smx, ?_, ?_⟩
        · rw [setupEval]
          dsimp only [tail]
          rw [WordSemStateFiniteExact.evaluate, s8get1]
          simp only [WordSemStateFiniteExact.getVarImm, s8get3, wordSemWordCmp, Encoders.Asm.wordCmpHOL,
            beq_self_eq_true]
          let p1 := a1 + StackRemove.bytesInWord width * count
          let p2 := a2 + StackRemove.bytesInWord width * count
          have amountLt : wordShiftAmount width < width := by
            rcases good with h | h <;> subst width <;> norm_num [wordShiftAmount]
          have amountMod : wordShiftAmount width % 2 ^ width = wordShiftAmount width := by
            apply Nat.mod_eq_of_lt
            rcases good with h | h <;> subst width <;> norm_num [wordShiftAmount]
          have shiftBytes : count <<< wordShiftAmount width = StackRemove.bytesInWord width * count := by
            rcases good with h | h
            · subst width
              have hp : BitVec.twoPow 32 2 = (4 : BitVec 32) := by decide
              simpa [wordShiftAmount, StackRemove.bytesInWord, hp] using (BitVec.twoPow_mul_eq_shiftLeft count 2).symm
            · subst width
              have hp : BitVec.twoPow 64 3 = (8 : BitVec 64) := by decide
              simpa [wordShiftAmount, StackRemove.bytesInWord, hp] using (BitVec.twoPow_mul_eq_shiftLeft count 3).symm
          have read11 : s8.getVar 11 = some (.word a1) := by
            simp [s8, s6, s3, s13, s1, s11, WordSemStateFiniteExact.getVar,
              WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
          have read13 : s8.getVar 13 = some (.word a2) := by
            simp [s8, s6, s3, s13, s1, s11, WordSemStateFiniteExact.getVar,
              WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
          have read6 : s8.getVar 6 = some (.word count) := by simpa [count] using s8get6
          have shiftExp : s8.wordExp (shiftN .lsl (.var 6) (wordShiftAmount width)) =
              some (.word (StackRemove.bytesInWord width * count)) := by
            simp [shiftN, WordSemStateFiniteExact.wordExp, read6, wordShiftHOL,
              amountMod, show ¬ width ≤ wordShiftAmount width by omega, shiftBytes]
          have p1Exp : s8.wordExp (.op .add [.var 11, shiftN .lsl (.var 6) (wordShiftAmount width)]) =
              some (.word p1) := by
            simp [WordSemStateFiniteExact.wordExp, read11, shiftExp, wordOpHOL, wordOp, theWords, p1]
          let s2 := s8.setVar 2 (.word p1)
          have shiftExp2 : s2.wordExp (shiftN .lsl (.var 6) (wordShiftAmount width)) =
              some (.word (StackRemove.bytesInWord width * count)) := by
            simp [shiftN, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
              s2, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, sl6,
              wordShiftHOL, amountMod, show ¬ width ≤ wordShiftAmount width by omega, count, shiftBytes]
          have p2Exp : s2.wordExp (.op .add [.var 13, shiftN .lsl (.var 6) (wordShiftAmount width)]) =
              some (.word p2) := by
            have reg : s2.getVar 13 = some (.word a2) := by
              simpa [s2, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                sptLookup_sptInsert_ne] using read13
            simp [WordSemStateFiniteExact.wordExp, reg, shiftExp2, wordOpHOL, wordOp, theWords, p2]
          let s4 := s2.setVar 4 (.word p2)
          rw [wordListSeq, seqAssign s8 2 _ (.word p1) _ p1Exp]
          change WordSemStateFiniteExact.evaluate _ s2 = _
          rw [wordListSeq, seqAssign s2 4 _ (.word p2) _ p2Exp]
          change WordSemStateFiniteExact.evaluate _ s4 = _
          have r0f : s4.getVar 0 = some (.loc l1 l2) := by
            simpa [s4, s2, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
              sptLookup_sptInsert_ne] using s8get0
          have r1f : s4.getVar 1 = some (.word x1) := by
            simpa [s4, s2, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
              sptLookup_sptInsert_ne] using s8get1
          have r6f : s4.getVar 6 = some (.word count) := by
            simpa [s4, s2, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
              sptLookup_sptInsert_ne] using read6
          have r2f : s4.getVar 2 = some (.word p1) := by
            simp [s4, s2, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
              sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
          have r4f : s4.getVar 4 = some (.word p2) := by
            simp [s4, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
          have codef : sptLookup compare1Location s4.code = some (4, compare1Code) := by
            simpa [s4, s2, s8, s6, s3, s13, s1, s11, WordSemStateFiniteExact.setVar] using code
          have sizef : sptLookup compare1Location s4.stackSize = sptLookup compare1Location t.stackSize := by rfl
          have clockf : s4.clock ≠ 0 := by
            have : t.clock ≠ 0 := by omega
            simpa [s4, s2, s8, s6, s3, s13, s1, s11, WordSemStateFiniteExact.setVar] using this
          rw [wordListSeq, WordSemStateFiniteExact.evaluate, r1f]
          simp only [WordSemStateFiniteExact.getVarImm]
          by_cases sign : x1 &&& (16 : BitVec width) = 0
          · have test : wordSemWordCmp .test (.word x1) (.word (16 : BitVec width)) = some true := by
              simp only [wordSemWordCmp, Encoders.Asm.wordCmpHOL, Option.some.injEq]
              change (x1 &&& (16 : BitVec width) == 0) = true
              exact beq_iff_eq.mpr sign
            rw [test]
            have entryEq : WordSemStateFiniteExact.callEnv [.loc l1 l2, .word count, .word p1, .word p2]
                (sptLookup compare1Location t.stackSize) (WordSemStateFiniteExact.decClock s4) = entry := by
              simp [entry, left, right, p1, p2, WordSemStateFiniteExact.callEnv,
                WordSemStateFiniteExact.decClock, s4, s2, s8, s6, s3, s13, s1, s11,
                WordSemStateFiniteExact.setVar]
              simp only [← BitVec.ofNat_eq_ofNat]
              rw [if_pos sign, if_pos sign]
            simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVars, r0f, r6f, r2f, r4f,
              wordSemBadDestArgs, wordSemAddRetLoc, wordSemFindCode, codef, sizef, clockf, entryEq, eval,
              wordSemBadFunReturn]
            simp [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock]
          · have test : wordSemWordCmp .test (.word x1) (.word (16 : BitVec width)) = some false := by
              simp only [wordSemWordCmp, Encoders.Asm.wordCmpHOL, Option.some.injEq]
              change (x1 &&& (16 : BitVec width) == 0) = false
              exact beq_eq_false_iff_ne.mpr sign
            rw [test]
            have entryEq : WordSemStateFiniteExact.callEnv [.loc l1 l2, .word count, .word p2, .word p1]
                (sptLookup compare1Location t.stackSize) (WordSemStateFiniteExact.decClock s4) = entry := by
              simp [entry, left, right, p1, p2, WordSemStateFiniteExact.callEnv,
                WordSemStateFiniteExact.decClock, s4, s2, s8, s6, s3, s13, s1, s11,
                WordSemStateFiniteExact.setVar]
              simp only [← BitVec.ofNat_eq_ofNat]
              rw [if_neg sign, if_neg sign]
            simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVars, r0f, r6f, r2f, r4f,
              wordSemBadDestArgs, wordSemAddRetLoc, wordSemFindCode, codef, sizef, clockf, entryEq, eval,
              wordSemBadFunReturn]
            simp [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock]
        · change optionLe smx (Option.map₂ max
            (wordSemOptionMax t.stackMax
              (wordSemOptionAdd (wordSemStackSize t.stack) (sptLookup compare1Location t.stackSize)))
            (Option.map₂ (· + ·) (wordSemStackSize t.stack) (sptLookup compare1Location t.stackSize))) at stackBound
          have opt : Option.map₂ max
              (wordSemOptionMax t.stackMax
                (wordSemOptionAdd (wordSemStackSize t.stack) (sptLookup compare1Location t.stackSize)))
              (Option.map₂ (· + ·) (wordSemStackSize t.stack) (sptLookup compare1Location t.stackSize)) =
              Option.map₂ max t.stackMax
                (Option.map₂ (· + ·) (wordSemStackSize t.stack) (sptLookup compare1Location t.stackSize)) := by
            cases t.stackMax <;> cases wordSemStackSize t.stack <;> cases sptLookup compare1Location t.stackSize <;>
              simp [wordSemOptionMax, wordSemOptionAdd]
          simpa [opt] using stackBound
      · have maskBeq (x : BitVec width) : ((x &&& BitVec.ofNat width 16) == BitVec.ofNat width 0) = decide (x &&& BitVec.ofNat width 16 = BitVec.ofNat width 0) := by
          by_cases h : x &&& BitVec.ofNat width 16 = BitVec.ofNat width 0
          · rw [h]
            rfl
          · have b : (x &&& BitVec.ofNat width 16 == BitVec.ofNat width 0) = false := beq_eq_false_iff_ne.mpr h
            rw [b]
            exact (decide_eq_false h).symm
        rw [if_neg headers] at cmpBody
        have hbeq : (x1 == x2) = false := beq_eq_false_iff_ne.mpr headers
        refine ⟨t.clock, t.stackMax, ?_, ?_⟩
        · rw [setupEval, cmpBody]
          by_cases sign1 : x1 &&& (16 : BitVec width) = 0 <;>
            by_cases sign2 : x2 &&& (16 : BitVec width) = 0 <;>
            by_cases shorter : WordGcFunctions.decodeLength conf x1 < WordGcFunctions.decodeLength conf x2 <;>
            simp [tail, result, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
              WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVars,
              WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
              WordSemStateFiniteExact.fixClock, WordSemStateFiniteExact.flushState,
              wordSemWordCmp, Encoders.Asm.wordCmpHOL, AndOp.and, maskBeq, sl1, sl3, sl6, sl8, sl0,
              sptLookup_sptInsert_ne, sptLookup_sptInsert_same, hbeq, shorter]
          all_goals
            simp only [← BitVec.ofNat_eq_ofNat]
            simp_all [s8, s6, s3, s13, s1, s11, WordSemStateFiniteExact.setVar]
        · exact (optionLe_max_right _ _ _).2 (Or.inl (optionLe_refl _))
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
