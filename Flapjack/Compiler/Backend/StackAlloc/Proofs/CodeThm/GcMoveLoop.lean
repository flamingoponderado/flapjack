import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GcMoveList
import Flapjack.Compiler.Backend.StackAlloc.Proofs.GcBitmaps

/-!
# `stack_allocProof` `word_gc_move_loop_code_thm`

`word_gc_move_loop_code_thm` of
`cakeml/compiler/backend/proofs/stack_allocProofScript.sml` (1050-1164): the
stackLang `word_gc_move_loop_code` loop run by the exact StackSem `evaluate`
simulates the shallow `word_gcFunctions` `word_gc_move_loop`. As in HOL, the
proof is a complete induction on the fuel `k`; a data object is skipped, and the
fields of a pointer object are moved by `word_gc_move_list_code_thm`, composed
with the induction hypothesis through `evaluate_add_clock`.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackRemove (loadInst storeInst leftShiftInst rightShiftInst)

/-- The `word_gc_move_loop_code` loop entry: the `While` test of register 3
against register 8. -/
theorem wordGcMoveLoopCode_eq {width : Nat} [NeZero width] (conf : Config) :
    (wordGcMoveLoopCode conf : HolProg width) =
      .loop (.ite .notEqual 3 (.reg 8)
        (.seq (loadInst 7 8)
          (.ite .test 7 (.imm 4)
            (.seq (rightShiftInst 7 (width - conf.lenSize))
              (.seq (addBytesInWordInst 8) (wordGcMoveListCode conf)))
            (.seq (rightShiftInst 7 (width - conf.lenSize))
              (.seq (add1Inst 7)
                (.seq (leftShiftInst 7 (wordShiftAmount width)) (addInst 8 7))))))
        (.break 0)) := rfl

/-- `Test` against `4w` reads bit 2 (HOL `word_bit_test` at `n = 2`). -/
theorem and_four_eq_zero_iff {width : Nat} (x : BitVec width) (hw : 2 < width) :
    x &&& 4#width = 0#width ↔ x.getLsbD 2 = false := by
  constructor
  · intro h
    have h4 : (4#width).getLsbD 2 = true := by
      rw [BitVec.getLsbD_ofNat]
      simp only [hw, decide_true, Bool.true_and]
      rfl
    have := congrArg (fun y => y.getLsbD 2) h
    simp only [BitVec.getLsbD_and, h4, Bool.and_true, BitVec.getLsbD_zero] at this
    exact this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    by_cases j2 : j = 2
    · subst j2; simp [BitVec.getLsbD_and, h]
    · have : Nat.testBit 4 j = false := by
        rw [show (4 : Nat) = 2 ^ 2 from rfl, Nat.testBit_two_pow]
        simp [Ne.symm j2]
      simp [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, this]

/-- One loop body on a data object (header bit 2 set): skip `len + 1` words. -/
theorem gcMoveLoop_body_skip {width : Nat} [NeZero width] {C F : Type} (conf : Config)
    (S : StackSemStateFiniteExact width C F) (pb x : BitVec width)
    (hws : wordShiftAmount width < width) (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0)
    (hshift : ∀ y : BitVec width, y <<< wordShiftAmount width = y * wordSemBytesInWord)
    (h8 : S.regs.lookup 8 = some (.word pb)) (hdm : S.mdomain pb = true)
    (hx : S.memory pb = .word x) (hbit : x.getLsbD 2 = true) :
    evaluate (.seq (loadInst 7 8)
      (.ite .test 7 (.imm 4)
        (.seq (rightShiftInst 7 (width - conf.lenSize))
          (.seq (addBytesInWordInst 8) (wordGcMoveListCode conf)))
        (.seq (rightShiftInst 7 (width - conf.lenSize))
          (.seq (add1Inst 7)
            (.seq (leftShiftInst 7 (wordShiftAmount width)) (addInst 8 7))))), S) =
      (none, setVar 8 (.word (pb + (decodeLength conf x + 1) * wordSemBytesInWord))
        (setVar 7 (.word ((decodeLength conf x + 1) * wordSemBytesInWord)) S)) := by
  have hpow : width < 2 ^ width := Nat.lt_two_pow_self
  have hws_le : ¬ width ≤ wordShiftAmount width := by omega
  have hwsm : wordShiftAmount width % 2 ^ width = wordShiftAmount width :=
    Nat.mod_eq_of_lt (by omega)
  have hlm : (width - conf.lenSize) % 2 ^ width = width - conf.lenSize :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (show width - conf.lenSize ≤ width by omega) hpow)
  have hl_le : ¬ width ≤ width - conf.lenSize := by omega
  have hdec : x >>> (width - conf.lenSize) = decodeLength conf x := rfl
  have h4 : (AndOp.and x (4#width) == 0#width) = false := by
    have : ¬ x &&& 4#width = 0#width := by
      rw [and_four_eq_zero_iff x hw2]; simp [hbit]
    have ha : ¬ AndOp.and x (4#width) = 0#width := this
    simpa using ha
  rw [evaluate_seq_none _ _ _ _ (loadInst_eval S 7 8 pb h8 hdm) le_rfl, evaluate_ite]
  simp [getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, wordSemWordCmp,
    wordCmpHOL, evaluate_seq, evaluate_inst, add1Inst, addInst, rightShiftInst, leftShiftInst,
    StackSemInst.instHOL, StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, setVar, wordOpHOL, wordOp, fixClock,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hx, h4, h8, hwsm, hlm, hws_le, hl_le,
    wordShiftHOL, hdec, hshift]
  apply regs_ext
  intro k
  simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  by_cases k7 : k = 7
  · subst k7; simp
  by_cases k8 : k = 8
  · subst k8; simp
  simp [k7, k8]

/-- One loop body on a pointer object (header bit 2 clear): run
`word_gc_move_list_code` over its `len` fields. -/
theorem gcMoveLoop_body_list {width : Nat} [NeZero width] {C F : Type} (conf : Config)
    (S : StackSemStateFiniteExact width C F) (pb x : BitVec width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0)
    (h8 : S.regs.lookup 8 = some (.word pb)) (hdm : S.mdomain pb = true)
    (hx : S.memory pb = .word x) (hbit : x.getLsbD 2 = false) :
    evaluate (.seq (loadInst 7 8)
      (.ite .test 7 (.imm 4)
        (.seq (rightShiftInst 7 (width - conf.lenSize))
          (.seq (addBytesInWordInst 8) (wordGcMoveListCode conf)))
        (.seq (rightShiftInst 7 (width - conf.lenSize))
          (.seq (add1Inst 7)
            (.seq (leftShiftInst 7 (wordShiftAmount width)) (addInst 8 7))))), S) =
      evaluate (wordGcMoveListCode conf, setVar 8 (.word (pb + wordSemBytesInWord))
        (setVar 7 (.word (decodeLength conf x)) S)) := by
  have hpow : width < 2 ^ width := Nat.lt_two_pow_self
  have hlm : (width - conf.lenSize) % 2 ^ width = width - conf.lenSize :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (show width - conf.lenSize ≤ width by omega) hpow)
  have hl_le : ¬ width ≤ width - conf.lenSize := by omega
  have hdec : x >>> (width - conf.lenSize) = decodeLength conf x := rfl
  have h4 : (AndOp.and x (4#width) == 0#width) = true := by
    have : x &&& 4#width = 0#width := (and_four_eq_zero_iff x hw2).2 hbit
    have ha : AndOp.and x (4#width) = 0#width := this
    simpa using ha
  rw [evaluate_seq_none _ _ _ _ (loadInst_eval S 7 8 pb h8 hdm) le_rfl, evaluate_ite]
  simp [getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, wordSemWordCmp,
    wordCmpHOL, evaluate_seq, evaluate_inst, addBytesInWordInst, rightShiftInst,
    StackSemInst.instHOL, StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, setVar, wordOpHOL, wordOp, fixClock,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hx, h4, h8, hlm, hl_le,
    wordShiftHOL, hdec]
  congr 3
  apply regs_ext
  intro k
  simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  by_cases k7 : k = 7
  · subst k7; simp
  by_cases k8 : k = 8
  · subst k8; simp
  simp [k7, k8]

/-- HOL's complete induction on the fuel `k`, with the source hypotheses. -/
theorem wordGcMoveLoopCode_run {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    ∀ (k : Nat) (pb i pa old : BitVec width) (c : Bool) (i2 pa2 : BitVec width)
      (m2 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F),
      wordGcMoveLoop k conf (pb, i, pa, old, s.memory, s.mdomain, c) = (i2, pa2, m2, true) →
      s.store.lookup .currHeap = some (.word old) → s.useStore = true →
      (s.regs.lookup 0).isSome = true → (s.regs.lookup 1).isSome = true →
      (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      (s.regs.lookup 7).isSome = true → s.regs.lookup 8 = some (.word pb) → c = true →
      ∃ ck r0 r1 r2 r5 r6 r7,
        evaluate (wordGcMoveLoopCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m2
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa2),
              (4, .word i2), (5, r5), (6, r6), (7, r7), (8, .word pa2)] }) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro pb i pa old c i2 pa2 m2 s hm hcurr huse h0 h1 h2 h3 h4 h5 h6 h7 h8 hc
  rw [wordGcMoveLoop] at hm
  by_cases hp : pb = pa
  · subst hp
    simp only [if_true, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl, -⟩ := hm
    obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.1 h0
    obtain ⟨r1, hr1⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨r2, hr2⟩ := Option.isSome_iff_exists.1 h2
    obtain ⟨r5, hr5⟩ := Option.isSome_iff_exists.1 h5
    obtain ⟨r6, hr6⟩ := Option.isSome_iff_exists.1 h6
    obtain ⟨r7, hr7⟩ := Option.isSome_iff_exists.1 h7
    refine ⟨0, r0, r1, r2, r5, r6, r7, ?_⟩
    rw [wordGcMoveLoopCode_eq, evaluate_loop, evaluate_ite, evaluate_break]
    simp only [getVar, HolRegImm.toWordRegImm, Nat.add_zero, h3]
    simp [StackSemStateOps.getVarImm, getVar, wordSemWordCmp, wordCmpHOL, fixClock, contLoop,
      StackSemControl.exitLoop, h8]
    apply regs_ext
    intro k
    simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl, FUPDATE_HOL]
    by_cases k0 : k = 0
    · subst k0; simp [hr0]
    by_cases k1 : k = 1
    · subst k1; simp [hr1]
    by_cases k2 : k = 2
    · subst k2; simp [hr2]
    by_cases k3 : k = 3
    · subst k3; simp [h3]
    by_cases k4 : k = 4
    · subst k4; simp [h4]
    by_cases k5 : k = 5
    · subst k5; simp [hr5]
    by_cases k6 : k = 6
    · subst k6; simp [hr6]
    by_cases k7 : k = 7
    · subst k7; simp [hr7]
    by_cases k8 : k = 8
    · subst k8; simp [h8]
    simp [k0, k1, k2, k3, k4, k5, k6, k7, k8]
  have hk : k ≠ 0 := by
    intro hk; subst hk; simp [hp] at hm
  simp only [hp, hk, if_false] at hm
  have hpb : (!(pa == pb)) = true := by simpa using Ne.symm hp
  by_cases hb : (wordSemTheWord (s.memory pb)).getLsbD 2 = true
  · simp only [hb, if_true] at hm
    have hc0 := wordGcMoveLoop_ok hm rfl
    simp only [Bool.and_eq_true] at hc0
    obtain ⟨-, hdm, hisw⟩ := hc0
    obtain ⟨x, hx⟩ := (isWord_thm _).1 hisw
    rw [hx] at hm hb
    simp only [wordSemTheWord] at hm hb
    have hc1 := wordGcMoveLoop_ok hm rfl
    let s5 : StackSemStateFiniteExact width C F :=
      setVar 8 (.word (pb + (decodeLength conf x + 1) * wordSemBytesInWord))
        (setVar 7 (.word ((decodeLength conf x + 1) * wordSemBytesInWord)) s)
    obtain ⟨ck, r0, r1, r2, r5, r6, r7, hr⟩ := ih (k - 1) (by omega) _ i pa old _ i2 pa2 m2 s5
      hm hcurr huse
      (by simpa [s5, setVar, FUPDATE_HOL] using h0) (by simpa [s5, setVar, FUPDATE_HOL] using h1)
      (by simpa [s5, setVar, FUPDATE_HOL] using h2) (by simp [s5, setVar, FUPDATE_HOL, h3])
      (by simp [s5, setVar, FUPDATE_HOL, h4]) (by simpa [s5, setVar, FUPDATE_HOL] using h5)
      (by simpa [s5, setVar, FUPDATE_HOL] using h6) (by simp [s5, setVar, FUPDATE_HOL])
      (by simp [s5, setVar, FUPDATE_HOL]) hc1
    refine ⟨ck + 1, r0, r1, r2, r5, r6, r7, ?_⟩
    rw [wordGcMoveLoopCode_eq, evaluate_loop, evaluate_ite]
    simp only [getVar, HolRegImm.toWordRegImm, h3, StackSemStateOps.getVarImm, h8,
      wordSemWordCmp, wordCmpHOL, hpb]
    rw [gcMoveLoop_body_skip conf { s with clock := s.clock + (ck + 1) } pb x hws hw2 hlen hshift
      h8 hdm hx hb]
    have hck : s.clock + (ck + 1) ≠ 0 := by omega
    simp only [fixClock, setVar, contLoop, Nat.min_self, if_true, hck, if_false, decClock,
      ← wordGcMoveLoopCode_eq]
    refine (congrArg (fun st => evaluate (wordGcMoveLoopCode conf, st)) ?_).trans (hr.trans ?_)
    · simp only [s5, setVar]
      congr 1
    · simp only [s5, setVar, Prod.mk.injEq, true_and]
      congr 1
      apply regs_ext
      intro k
      simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl,
        FUPDATE_HOL, HolFiniteMapExact.lookup_updateEq]
      by_cases k7 : k = 7
      · subst k7; simp
      by_cases k8 : k = 8
      · subst k8; simp
      simp [k7, k8]
  · simp only [hb, Bool.false_eq_true, if_false] at hm
    generalize hl : wordGcMoveList conf (pb + wordSemBytesInWord,
      decodeLength conf (wordSemTheWord (s.memory pb)), i, pa, old, s.memory, s.mdomain) = R at hm
    obtain ⟨pb3, i1, pa1, m1, c1⟩ := R
    simp only at hm
    have hc0 := wordGcMoveLoop_ok hm rfl
    simp only [Bool.and_eq_true] at hc0
    obtain ⟨⟨-, hdm, hisw⟩, hc1⟩ := hc0
    subst hc1
    obtain ⟨x, hx⟩ := (isWord_thm _).1 hisw
    rw [hx] at hm hb hl
    simp only [wordSemTheWord] at hm hb hl
    have hb' : x.getLsbD 2 = false := by simpa using hb
    have hc2 := wordGcMoveLoop_ok hm rfl
    let s5 : StackSemStateFiniteExact width C F :=
      setVar 8 (.word (pb + wordSemBytesInWord)) (setVar 7 (.word (decodeLength conf x)) s)
    obtain ⟨ck, q0, q1, q2, q5, q6, hL⟩ := word_gc_move_list_code_thm (decodeLength conf x)
      (pb + wordSemBytesInWord) s5 pa1 pa old m1 s.memory i1 i s.mdomain conf pb3
      ⟨hl, hsl, hws, hw2, hlen, hshift, hcurr, huse, rfl, rfl,
        by simpa [s5, setVar, FUPDATE_HOL] using h0, by simpa [s5, setVar, FUPDATE_HOL] using h1,
        by simpa [s5, setVar, FUPDATE_HOL] using h2, by simp [s5, getVar, setVar, FUPDATE_HOL, h3],
        by simp [s5, getVar, setVar, FUPDATE_HOL, h4], by simpa [s5, setVar, FUPDATE_HOL] using h5⟩
      (by simpa [s5, setVar, FUPDATE_HOL] using h6)
      ⟨by simp [s5, getVar, setVar, FUPDATE_HOL], by simp [s5, getVar, setVar, FUPDATE_HOL]⟩
    let s6 : StackSemStateFiniteExact width C F :=
      { s5 with
        memory := m1
        regs := s5.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa1),
          (4, .word i1), (5, q5), (6, q6), (7, .word 0), (8, .word pb3)] }
    obtain ⟨ck', r0, r1, r2, r5, r6, r7, hr⟩ := ih (k - 1) (by omega) pb3 i1 pa1 old _ i2 pa2 m2 s6
      hm hcurr huse
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      hc2
    refine ⟨ck + ck' + 1, r0, r1, r2, r5, r6, r7, ?_⟩
    have hadd := StackProps.evaluateAddClock (ck' + 1) _ _ _ _ ⟨hL, by simp⟩
    have hs5 : setVar 8 (.word (pb + wordSemBytesInWord)) (setVar 7 (.word (decodeLength conf x))
        { s with clock := s.clock + (ck + ck' + 1) }) =
        { { s5 with clock := s5.clock + ck } with
          clock := { s5 with clock := s5.clock + ck }.clock + (ck' + 1) } := by
      simp only [s5, setVar]
      congr 1
      omega
    rw [wordGcMoveLoopCode_eq, evaluate_loop, evaluate_ite]
    simp only [getVar, HolRegImm.toWordRegImm, h3, StackSemStateOps.getVarImm, h8,
      wordSemWordCmp, wordCmpHOL, hpb]
    rw [gcMoveLoop_body_list conf { s with clock := s.clock + (ck + ck' + 1) } pb x hw2 hlen
      h8 hdm hx hb', hs5, hadd]
    have hs5c : s5.clock = s.clock := rfl
    have hmin : min (s.clock + (ck + ck' + 1)) (s5.clock + (ck' + 1)) = s5.clock + (ck' + 1) := by
      omega
    have hck : s5.clock + (ck' + 1) ≠ 0 := by omega
    simp only [fixClock, contLoop, hmin, if_true, hck, if_false, decClock,
      ← wordGcMoveLoopCode_eq]
    refine (congrArg (fun st => evaluate (wordGcMoveLoopCode conf, st)) ?_).trans (hr.trans ?_)
    · congr 1
    · simp only [s6, s5, setVar, Prod.mk.injEq, true_and]
      congr 1
      apply regs_ext
      intro k
      simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl,
        FUPDATE_HOL, HolFiniteMapExact.lookup_updateEq]
      by_cases k0 : k = 0
      · subst k0; simp
      by_cases k1 : k = 1
      · subst k1; simp
      by_cases k2 : k = 2
      · subst k2; simp
      by_cases k3 : k = 3
      · subst k3; simp
      by_cases k4 : k = 4
      · subst k4; simp
      by_cases k5 : k = 5
      · subst k5; simp
      by_cases k6 : k = 6
      · subst k6; simp
      by_cases k7 : k = 7
      · subst k7; simp
      by_cases k8 : k = 8
      · subst k8; simp
      simp [k0, k1, k2, k3, k4, k5, k6, k7, k8]

namespace GcMoveLoopSupport

/-- Canonical finite-support codec of the owning StackSem state carrier, required
by the `fmap_as_finite_support` qualifier of `word_gc_move_loop_code_thm`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

end GcMoveLoopSupport

/-- Exact HOL `word_gc_move_loop_code_thm` (`stack_allocProofScript.sml:1050-1164`),
with HOL's binder order and its four curried premise groups; HOL's free `conf`
is implicit. `FLOOKUP s.store CurrHeap`, `k IN FDOM s.regs`, `|++` and `get_var`
are the canonical carrier's lookups, `updateListEq` and `getVar`; the
existentials `ck r0 r1 r2 r5 r6 r7` are kept. HOL's `conf.len_size + 2 <
dimindex` premise is retained although this proof does not use it. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gc_move_loop_code_thm"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_gc_move_loop_code_thm {width : Nat} [NeZero width] {C F : Type} {conf : Config} :
    ∀ (k : Nat) (pb1 i1 pa1 old1 : BitVec width) (m1 : BitVec width → WordLocW width)
      (dm1 : BitVec width → Bool) (c1 : Bool) (i2 pa2 : BitVec width)
      (m2 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F),
      wordGcMoveLoop k conf (pb1, i1, pa1, old1, m1, dm1, c1) = (i2, pa2, m2, true) ∧
        shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
        conf.lenSize ≠ 0 ∧ conf.lenSize + 2 < width ∧
        (∀ w : BitVec width, w <<< wordShiftAmount width = w * wordSemBytesInWord) ∧
        s.store.lookup .currHeap = some (.word old1) ∧ s.useStore = true ∧
        s.memory = m1 ∧ s.mdomain = dm1 ∧
        (s.regs.lookup 0).isSome = true ∧ (s.regs.lookup 1).isSome = true ∧
        (s.regs.lookup 2).isSome = true ∧
        getVar 3 s = some (.word pa1) ∧ getVar 4 s = some (.word i1) ∧
        (s.regs.lookup 5).isSome = true →
      (s.regs.lookup 6).isSome = true →
      (s.regs.lookup 7).isSome = true →
      getVar 8 s = some (.word pb1) ∧ c1 = true →
      ∃ ck r0 r1 r2 r5 r6 r7,
        evaluate (wordGcMoveLoopCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m2
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa2),
              (4, .word i2), (5, r5), (6, r6), (7, r7), (8, .word pa2)] }) := by
  rintro k pb1 i1 pa1 old1 m1 dm1 c1 i2 pa2 m2 s
    ⟨hm, hsl, hws, hw2, hlen, -, hshift, hcurr, huse, rfl, rfl, h0, h1, h2, h3, h4, h5⟩ h6 h7
    ⟨h8, hc⟩
  exact wordGcMoveLoopCode_run hsl hws hw2 hlen hshift k pb1 i1 pa1 old1 c1 i2 pa2 m2 s hm
    hcurr huse h0 h1 h2 (by simpa [getVar] using h3) (by simpa [getVar] using h4) h5 h6 h7
    (by simpa [getVar] using h8) hc

end Flapjack.Compiler.Backend.StackAlloc
