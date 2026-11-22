module

public import Flapjack.Compiler.Backend.DataToWord.Stubs
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.BasicLemmas
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.RealAddress
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockHeader
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockStack
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Rearrange
public import Flapjack.Compiler.Backend.Semantics.DataProps.ValueList
public import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate
public import Flapjack.Compiler.Backend.BackendProps
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.WordLemmas

@[expose] public section

/-! # `evaluate_AppendLenLoop_code` of `data_to_word_assignProofScript.sml` -/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

namespace AppendLenLoopWitness

/-- Canonical finite-map roundtrip for the word-state fields. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end AppendLenLoopWitness

/-- The length-counting loop of list append walks the list, adding 12 per cell.

The evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "evaluate_AppendLenLoop_code" 5283
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateAppendLenLoopCode {width : Nat} [NeZero width] {C F : Type}
    (refs : Spt (BvlSem.Ref DataSem.Value)) (sp : Nat) :
    ∀ (k : Nat) (t : WordSemStateFiniteExact width C F) (c : Config) (xs : List DataSem.Value)
      (l1 l2 : Nat) (w : BitVec width) (vars : List (DataSem.Value × WordLocW width)) (ts : Nat)
      (v : DataSem.Value),
      memoryRel c t.be ts refs sp t.store t.memory t.mdomain ((v, .word w) :: vars) ∧
      DataSem.valueToList v = some xs ∧
      sptLookup 0 t.locals = some (.loc l1 l2) ∧
      sptLookup 2 t.locals = some (.word w) ∧
      sptLookup 4 t.locals = some (.word (BitVec.ofNat width (12 * k))) ∧
      sptLookup appendLenLoopLocation t.code = some (3, appendLenLoopCode c) ∧
      t.localsSize = sptLookup appendLenLoopLocation t.stackSize ∧
      goodDimindex width ∧
      xs.length ≤ t.clock →
      ∃ locals smx,
        (match WordSemStateFiniteExact.evaluate (appendLenLoopCode c) t with
          | (res, s) => if wordSemBadFunReturn res then (some WordSemResult.error, s) else (res, s)) =
        (match WordSemStateFiniteExact.evaluate (appendLenLoopCode c)
            {t with locals := locals, clock := t.clock - xs.length, stackMax := smx} with
          | (res, s) => if wordSemBadFunReturn res then (some WordSemResult.error, s) else (res, s)) ∧
        sptLookup 0 locals = some (.loc l1 l2) ∧
        sptLookup 2 locals = some (.word 2) ∧
        sptLookup 4 locals = some (.word (BitVec.ofNat width (12 * (k + xs.length)))) ∧
        optionLe t.stackMax smx ∧
        optionLe smx (Option.map₂ max t.stackMax
          (Option.map₂ (· + ·) (wordSemStackSize t.stack)
            (sptLookup appendLenLoopLocation t.stackSize))) := by
  intro k t c xs
  induction xs generalizing k t with
  | nil =>
    rintro l1 l2 w vars ts v ⟨rel, list, h0, h2, h4, hcode, hsize, good, hclock⟩
    obtain ⟨tsv, rfl⟩ := (valueToList_eq_some_nil v).1 list
    obtain ⟨w', hw, small⟩ := memoryRel_blockImp c t.be ts refs sp t.store t.memory t.mdomain
      tsv 0 [] (.word w) vars ⟨rel, good⟩
    simp only [if_true] at small
    cases hw
    refine ⟨t.locals, t.stackMax, ?_, h0, ?_, by simpa using h4, ?_, ?_⟩
    · simp
    · rw [h2, small.1]; simp
    · cases t.stackMax <;> simp [optionLe]
    · cases hm : t.stackMax <;> cases (Option.map₂ (· + ·) (wordSemStackSize t.stack)
          (sptLookup appendLenLoopLocation t.stackSize)) <;> simp [optionLe, Option.map₂]
  | cons x xs ih =>
    rintro l1 l2 w vars ts v ⟨rel, list, h0, h2, h4, hcode, hsize, good, hclock⟩
    obtain ⟨tsv, ys, rfl, ysList⟩ := DataSem.valueToList_cons list
    obtain ⟨w', hw, hdr⟩ := memoryRel_blockImp c t.be ts refs sp t.store t.memory t.mdomain
      tsv BackendCommon.consTag [x, ys] (.word w) vars ⟨rel, good⟩
    cases hw
    simp only [reduceCtorEq, if_false] at hdr
    obtain ⟨a, hx, lsb, -, -, addr, -, -, -⟩ := hdr
    obtain ⟨w2, a2, off, offEq, locEq, addrEq, dom, rel2⟩ :=
      memoryRel_blockMem c t.be ts refs sp t.store t.memory t.mdomain tsv BackendCommon.consTag
        [x, ys] (.word w) vars 1 (by simp) ⟨rel, good⟩
    cases locEq
    rw [addr] at addrEq
    cases addrEq
    rw [getRealOffset_smallnum 1 good] at offEq
    cases offEq
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at rel2
    have ysBlock : ∃ tsy tagy vsy, ys = .block tsy tagy vsy := by
      cases xs with
      | nil =>
        obtain ⟨tsy, rfl⟩ := (valueToList_eq_some_nil ys).1 ysList
        exact ⟨_, _, _, rfl⟩
      | cons _ _ =>
        obtain ⟨tsy, zs, rfl, -⟩ := DataSem.valueToList_cons ysList
        exact ⟨_, _, _, rfl⟩
    obtain ⟨tsy, tagy, vsy, rfl⟩ := ysBlock
    obtain ⟨xx, hxx, -⟩ := memoryRel_blockImp c t.be ts refs sp t.store t.memory t.mdomain
      tsy tagy vsy _ _ ⟨rel2, good⟩
    have shiftOk : shiftLength c < width := by
      obtain ⟨_, _, _, _, _, _, heapMem, _⟩ := rel
      exact heapMem.2.2.2.2.2.1
    have bytes2 : StackRemove.bytesInWord width + BitVec.ofNat width 1 * StackRemove.bytesInWord width =
        BitVec.ofNat width 2 * (wordSemBytesInWord : BitVec width) := by
      simp only [StackRemove.bytesInWord, wordSemBytesInWord]
      generalize BitVec.ofNat width (width / 8) = b
      rw [BitVec.one_mul, BitVec.two_mul]
    rw [bytes2] at dom hxx rel2
    have testFalse : Compiler.Encoders.Asm.wordCmpHOL .test w 1 = false := by
      have := (word_and_one_eq_0_iff w).not
      simp only [lsb, not_true_eq_false, not_false_eq_true, iff_true] at this
      simpa [Compiler.Encoders.Asm.wordCmpHOL, AndOp.and] using this
    let size := sptLookup appendLenLoopLocation t.stackSize
    let k12 : BitVec width := BitVec.ofNat width (12 * k) + 12
    let ttt := WordSemStateFiniteExact.callEnv [.loc l1 l2, .word xx, .word k12] size
      (WordSemStateFiniteExact.decClock
        {t with locals := sptInsert 4 (.word k12) (sptInsert 2 (.word xx) t.locals)})
    have clockPositive : t.clock ≠ 0 := by simp at hclock; omega
    have run : WordSemStateFiniteExact.evaluate (appendLenLoopCode c) t =
        (match WordSemStateFiniteExact.evaluate (appendLenLoopCode c) ttt with
          | (res, s) => if wordSemBadFunReturn res then (some WordSemResult.error, s) else (res, s)) := by
      have ra := getRealAddr_lemma c 2 t w a ⟨shiftOk, good, by simpa [WordSemStateFiniteExact.getVar] using h2, addr⟩
      conv => lhs; unfold appendLenLoopCode
      simp only [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
        WordSemStateFiniteExact.getVar, wordSemWordCmp, h2, testFalse]
      simp [wordListSeq, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.fixClock,
        WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.memLoad,
        WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
        sptLookup_sptInsert_same, sptLookup_sptInsert_ne, theWords, wordOpHOL, wordOp, ra, dom, hxx,
        h0, h4]
      simp [wordSemBadDestArgs, wordSemAddRetLoc, wordSemFindCode, hcode, clockPositive]
      rfl
    have len : (x :: xs).length = xs.length + 1 := rfl
    have k12Eq : k12 = BitVec.ofNat width (12 * (k + 1)) := by
      simp only [k12, Nat.mul_add, Nat.mul_one]
      rw [BitVec.ofNat_add]; rfl
    have relNext : memoryRel c ttt.be ts refs sp ttt.store ttt.memory ttt.mdomain
        ((.block tsy tagy vsy, .word xx) :: vars) := by
      rw [hxx] at rel2
      exact memoryRel_rearrange c t.be ts refs sp t.store t.memory t.mdomain _ _
        (by intro pair mem; simp at mem; rcases mem with h | h <;> simp [h]) rel2
    obtain ⟨locals, smx, eq, l0, l2', l4, le1, le2⟩ := ih (k + 1) ttt l1 l2 xx vars ts (.block tsy tagy vsy)
      ⟨relNext, ysList,
        by simp [ttt, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup],
        by simp [ttt, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup],
        by simp [ttt, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup, k12Eq],
        hcode, rfl, good,
        by simp only [ttt, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock]; omega⟩
    have wrapIdem : ∀ r : Option (WordSemResult width) × WordSemStateFiniteExact width C F,
        (match (match r with
          | (res, s) => if wordSemBadFunReturn res then (some WordSemResult.error, s) else (res, s)) with
          | (res, s) => if wordSemBadFunReturn res then (some WordSemResult.error, s) else (res, s)) =
        (match r with
          | (res, s) => if wordSemBadFunReturn res then (some WordSemResult.error, s) else (res, s)) := by
      rintro ⟨res, s⟩
      by_cases h : wordSemBadFunReturn res = true
      · simp only [h, if_true]
        rfl
      · simp only [h, if_false, Bool.false_eq_true]
    have stEq : {ttt with locals := locals, clock := ttt.clock - xs.length, stackMax := smx} =
        {t with locals := locals, clock := t.clock - (x :: xs).length, stackMax := smx} := by
      simp only [ttt, size, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock, ← hsize, len]
      congr 1
      omega
    refine ⟨locals, smx, ?_, l0, l2', ?_, ?_, ?_⟩
    · rw [run, wrapIdem, eq, stEq]
    · rw [l4, len, Nat.add_assoc, Nat.add_comm 1]
    all_goals
      have optMax (a b : Option Nat) : wordSemOptionMax a b = Option.map₂ max a b := by
        cases a <;> cases b <;> rfl
      have optAdd (a b : Option Nat) : wordSemOptionAdd a b = Option.map₂ (· + ·) a b := by
        cases a <;> cases b <;> rfl
      simp only [ttt, size, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
        optMax, optAdd] at le1 le2
      revert le1 le2
      generalize t.stackMax = m0
      generalize wordSemStackSize t.stack = st
      generalize sptLookup appendLenLoopLocation t.stackSize = sz
      cases m0 <;> cases st <;> cases sz <;> cases smx <;> simp [optionLe, Option.map₂] <;> omega

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
