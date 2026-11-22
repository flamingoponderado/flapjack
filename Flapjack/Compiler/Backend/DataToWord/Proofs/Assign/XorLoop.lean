module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.XorWords
public import Flapjack.Compiler.Backend.DataToWord.Stubs
public import Flapjack.Compiler.Backend.DataToWord.Control
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
public import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate

@[expose] public section

/-! # `evaluate_XorLoop` of `data_to_word_assignProofScript.sml` -/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.SemanticPrimitivesHOL

namespace XorLoopWitness

/-- Canonical finite-map roundtrip for the word-state fields. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end XorLoopWitness

/-- A checked `read_word` exposes a word; local proof infrastructure for
`evaluate_XorLoop`. -/
private theorem readWord_word {width : Nat} [NeZero width] (w : WordLocW width)
    (ok : wordSemIsWordLoc w = true) : ∃ x, w = .word x := by
  cases w with
  | word x => exact ⟨x, rfl⟩
  | loc x y => simp [wordSemIsWordLoc] at ok

/-- Invert a guarded success; local proof infrastructure for `evaluate_XorLoop`. -/
private theorem iteNoneRight {α : Type} {c : Prop} [Decidable c] {x : Option α} {y : α}
    (h : (if c then x else none) = some y) : c ∧ x = some y := by
  split at h
  · exact ⟨by assumption, h⟩
  · simp at h

/-- The generated word-wise XOR loop implements the original memory XOR.
The evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "evaluate_XorLoop"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateXorLoop {width : Nat} [NeZero width] {C F : Type}
    (a1 a2 l : BitVec width) (dm : BitVec width → Bool) (m : BitVec width → WordLocW width)
    (l1 l2 : Nat) (t1 : WordSemStateFiniteExact width C F) (m1 : BitVec width → WordLocW width)
    (premises : wordXorBytes a1 a2 l dm m = some m1 ∧ t1.memory = m ∧ t1.mdomain = dm ∧
      l.toNat < t1.clock ∧ goodDimindex width ∧
      sptLookup xorLoopLocation t1.code = some (4, xorLoopCode) ∧
      WordSemStateFiniteExact.getVar 0 t1 = some (.loc l1 l2) ∧
      WordSemStateFiniteExact.getVar 2 t1 = some (.word a2) ∧
      WordSemStateFiniteExact.getVar 4 t1 = some (.word a1) ∧
      WordSemStateFiniteExact.getVar 6 t1 = some (.word l)) :
    ∃ clock maxStack,
      WordSemStateFiniteExact.evaluate xorLoopCode t1 =
        (some (.result (.loc l1 l2) [.word 2]),
          {t1 with memory := m1, clock := clock, stackMax := maxStack, locals := .ln, localsSize := some 0}) ∧
      (maxStack ≠ t1.stackMax → maxStack = Option.map₂ max t1.stackMax
        (Option.map₂ (· + ·) (wordSemStackSize t1.stack) (sptLookup xorLoopLocation t1.stackSize))) := by
  obtain ⟨n, hn⟩ : ∃ n, l.toNat = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing a1 a2 l dm m t1 with
  | _ n ih =>
  obtain ⟨loop, hmem, hdom, hclock, good, hcode, h0, h2, h4, h6⟩ := premises
  subst hmem hdom
  change sptLookup 0 t1.locals = some (.loc l1 l2) at h0
  change sptLookup 2 t1.locals = some (.word a2) at h2
  change sptLookup 4 t1.locals = some (.word a1) at h4
  change sptLookup 6 t1.locals = some (.word l) at h6
  have two : (2 : BitVec width).toNat = 2 := by
    rcases good with h | h <;> subst h <;> rfl
  have twoMod : 2 % 2 ^ width = 2 := by
    rcases good with h | h <;> subst h <;> rfl
  have oneMod : 1 % 2 ^ width = 1 := by
    rcases good with h | h <;> subst h <;> rfl
  have oneNe : (BitVec.ofNat width 1 == BitVec.ofNat width 0) = false := by
    rcases good with h | h <;> subst h <;> rfl
  rw [wordXorBytes] at loop
  by_cases small : l.toNat < 2
  · simp only [two, small, true_or, if_true] at loop
    have lower : Compiler.Encoders.Asm.wordCmpHOL .lower l 2 = true := by
      simp [Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, twoMod, small]
    by_cases zero : l = 0
    · subst zero
      simp at loop
      subst loop
      refine ⟨t1.clock, t1.stackMax, ?_, by simp⟩
      simp [xorLoopCode, wordListSeq, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
        WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.flushState,
        WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.fixClock,
        wordSemWordCmp, h0, h6, twoMod, Compiler.Encoders.Asm.wordCmpHOL,
        sptLookup_sptInsert_same, sptLookup_sptInsert_ne]
    · simp only [zero, if_false, readWord] at loop
      obtain ⟨ok, loop⟩ := iteNoneRight loop
      simp only [Bool.and_eq_true] at ok
      obtain ⟨⟨d1, i1⟩, d2, i2⟩ := ok
      obtain ⟨x1, hm1⟩ := readWord_word _ i1
      obtain ⟨x2, hm2⟩ := readWord_word _ i2
      simp only [hm1, hm2, wordSemTheWord, Option.some.injEq] at loop
      subst loop
      have one : l = 1 := by
        apply BitVec.eq_of_toNat_eq
        have : l.toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq (by simpa using h))
        have h1 : (1 : BitVec width).toNat = 1 := by rcases good with h | h <;> subst h <;> rfl
        omega
      subst one
      refine ⟨t1.clock, t1.stackMax, ?_, by simp⟩
      simp [xorLoopCode, wordListSeq, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
        WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.flushState,
        WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.fixClock,
        WordSemStateFiniteExact.memLoad, WordSemStateFiniteExact.memStore,
        wordSemWordCmp, h0, h2, h4, h6, twoMod, oneMod, oneNe, Compiler.Encoders.Asm.wordCmpHOL,
        sptLookup_sptInsert_same, sptLookup_sptInsert_ne, d1, d2, hm1, hm2, theWords, wordOpHOL, wordOp]
  · have notSmall : ¬ (l.toNat < (2 : BitVec width).toNat ∨ ¬ goodDimindex width) := by
      rw [two]
      exact fun h => h.elim small (fun h' => h' good)
    simp only [notSmall, if_false, readWord, wordSemBytesInWord] at loop
    obtain ⟨ok, loop⟩ := iteNoneRight loop
    simp only [Bool.and_eq_true, and_assoc] at ok
    obtain ⟨d1, i1, d2, i2, d3, i3, d4, i4⟩ := ok
    obtain ⟨x1, hm1⟩ := readWord_word _ i1
    obtain ⟨x2, hm2⟩ := readWord_word _ i2
    obtain ⟨x3, hm3⟩ := readWord_word _ i3
    obtain ⟨x4, hm4⟩ := readWord_word _ i4
    simp only [hm1, hm2, hm3, hm4, wordSemTheWord] at loop
    let b : BitVec width := BitVec.ofNat width (width / 8)
    let mem' : BitVec width → WordLocW width := fun k =>
      if k = a2 + b then .word (x3 ^^^ x4) else if k = a2 then .word (x1 ^^^ x2) else t1.memory k
    let size := sptLookup xorLoopLocation t1.stackSize
    let next := WordSemStateFiniteExact.callEnv
      [.loc l1 l2, .word (a2 + 2 * b), .word (a1 + 2 * b), .word (l - 2)] size
      {t1 with clock := t1.clock - 1, memory := mem'}
    have twoLe : (2 : BitVec width) ≤ l := by
      rw [BitVec.le_def, two]
      omega
    have subNat : (l - 2).toNat = l.toNat - 2 := by
      rw [BitVec.toNat_sub_of_le twoLe, two]
    have nextPremises : wordXorBytes (a1 + 2 * b) (a2 + 2 * b) (l - 2) t1.mdomain mem' = some m1 ∧
        next.memory = mem' ∧ next.mdomain = t1.mdomain ∧ (l - 2).toNat < next.clock ∧ goodDimindex width ∧
        sptLookup xorLoopLocation next.code = some (4, xorLoopCode) ∧
        WordSemStateFiniteExact.getVar 0 next = some (.loc l1 l2) ∧
        WordSemStateFiniteExact.getVar 2 next = some (.word (a2 + 2 * b)) ∧
        WordSemStateFiniteExact.getVar 4 next = some (.word (a1 + 2 * b)) ∧
        WordSemStateFiniteExact.getVar 6 next = some (.word (l - 2)) := by
      refine ⟨loop, rfl, rfl, ?_, good, hcode, ?_, ?_, ?_, ?_⟩
      · simp only [next, WordSemStateFiniteExact.callEnv]
        omega
      all_goals simp [next, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar,
        sptFromList2, sptInsert, sptLookup]
    obtain ⟨outClock, outMax, nextRun, stackBound⟩ :=
      ih (l - 2).toNat (by omega) (a1 + 2 * b) (a2 + 2 * b) (l - 2) t1.mdomain mem' next nextPremises rfl
    have resultEq : WordSemStateFiniteExact.evaluate xorLoopCode next =
        (some (.result (.loc l1 l2) [.word 2]),
          {t1 with memory := m1, clock := outClock, stackMax := outMax, locals := .ln, localsSize := some 0}) := by
      simpa [next, WordSemStateFiniteExact.callEnv] using nextRun
    refine ⟨outClock, outMax, ?_, ?_⟩
    · have testFalse : Compiler.Encoders.Asm.wordCmpHOL .lower l 2 = false := by
        simp [Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, twoMod, small]
      simp only [xorLoopCode, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
        WordSemStateFiniteExact.getVar, wordSemWordCmp, h6, testFalse]
      simp [wordListSeq, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.fixClock,
        WordSemStateFiniteExact.getVars,
        WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.memLoad, WordSemStateFiniteExact.memStore,
        WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
        sptLookup_sptInsert_same, sptLookup_sptInsert_ne, theWords, wordOpHOL, wordOp,
        h0, h2, h4, h6, d1, d2, d3, d4, hm1, hm2, hm3, hm4]
      have clockPositive : t1.clock ≠ 0 := by omega
      simp [wordSemBadDestArgs, wordSemAddRetLoc, wordSemFindCode, hcode, clockPositive,
        WordSemStateFiniteExact.decClock, wordSemBadFunReturn]
      simp only [next, WordSemStateFiniteExact.callEnv, size, mem', b, BitVec.ofNat_eq_ofNat] at resultEq
      simp only [WordSemStateFiniteExact.callEnv]
      simp only [resultEq]
      rfl
    · simp only [next, WordSemStateFiniteExact.callEnv, size] at stackBound
      have optMax (a b : Option Nat) : wordSemOptionMax a b = Option.map₂ max a b := by
        cases a <;> cases b <;> rfl
      have optAdd (a b : Option Nat) : wordSemOptionAdd a b = Option.map₂ (· + ·) a b := by
        cases a <;> cases b <;> rfl
      have idem (a b : Option Nat) : Option.map₂ max (Option.map₂ max a b) b = Option.map₂ max a b := by
        cases a <;> cases b <;> simp [Option.map₂]
      rw [optMax, optAdd, idem] at stackBound
      intro _
      by_contra hn
      exact hn (stackBound hn)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
