import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GcMoveLoop
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenGcMoveList

/-!
# `stack_allocProof` `word_gen_gc_move_data_code_thm`

`word_gen_gc_move_data_code_thm` of
`cakeml/compiler/backend/proofs/stack_allocProofScript.sml` (3992-4122): the
generational counterpart of `word_gc_move_loop_code_thm`. The stackLang
`word_gen_gc_move_data_code` loop run by the exact StackSem `evaluate` simulates
`word_gen_gc_move_data`. As in HOL, the proof is a complete induction on the fuel
`k`; data objects are skipped, and pointer objects' fields are moved by
`word_gen_gc_move_list_code_thm`, composed with the induction hypothesis through
`evaluate_add_clock`, threading the `Temp 0w`-`Temp 3w` store slots.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackRemove (loadInst storeInst leftShiftInst rightShiftInst)

/-- The `word_gen_gc_move_data_code` loop entry: the `While` test of register 3
against register 8. -/
theorem wordGenGcMoveDataCode_eq {width : Nat} [NeZero width] (conf : Config) :
    (wordGenGcMoveDataCode conf : HolProg width) =
      .loop (.ite .notEqual 3 (.reg 8)
        (.seq (loadInst 7 8)
          (.ite .test 7 (.imm 4)
            (.seq (rightShiftInst 7 (width - conf.lenSize))
              (.seq (addBytesInWordInst 8) (wordGenGcMoveListCode conf)))
            (.seq (rightShiftInst 7 (width - conf.lenSize))
              (.seq (add1Inst 7)
                (.seq (leftShiftInst 7 (wordShiftAmount width)) (addInst 8 7))))))
        (.break 0)) := rfl

/-- One data-loop body on a data object (header bit 2 set), for any field-moving
program `G`: skip `len + 1` words. -/
theorem dataBody_skip {width : Nat} [NeZero width] {C F : Type} (conf : Config)
    (G : HolProg width) (S : StackSemStateFiniteExact width C F) (pb x : BitVec width)
    (hws : wordShiftAmount width < width) (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0)
    (hshift : ∀ y : BitVec width, y <<< wordShiftAmount width = y * wordSemBytesInWord)
    (h8 : S.regs.lookup 8 = some (.word pb)) (hdm : S.mdomain pb = true)
    (hx : S.memory pb = .word x) (hbit : x.getLsbD 2 = true) :
    evaluate (.seq (loadInst 7 8)
      (.ite .test 7 (.imm 4)
        (.seq (rightShiftInst 7 (width - conf.lenSize)) (.seq (addBytesInWordInst 8) G))
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

/-- One data-loop body on a pointer object (header bit 2 clear), for any
field-moving program `G`: run `G` over its `len` fields. -/
theorem dataBody_list {width : Nat} [NeZero width] {C F : Type} (conf : Config)
    (G : HolProg width) (S : StackSemStateFiniteExact width C F) (pb x : BitVec width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0)
    (h8 : S.regs.lookup 8 = some (.word pb)) (hdm : S.mdomain pb = true)
    (hx : S.memory pb = .word x) (hbit : x.getLsbD 2 = false) :
    evaluate (.seq (loadInst 7 8)
      (.ite .test 7 (.imm 4)
        (.seq (rightShiftInst 7 (width - conf.lenSize)) (.seq (addBytesInWordInst 8) G))
        (.seq (rightShiftInst 7 (width - conf.lenSize))
          (.seq (add1Inst 7)
            (.seq (leftShiftInst 7 (wordShiftAmount width)) (addInst 8 7))))), S) =
      evaluate (G, setVar 8 (.word (pb + wordSemBytesInWord))
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
theorem wordGenGcMoveDataCode_run {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord)
    (old : BitVec width) :
    ∀ (k : Nat) (ha i pa ib pb i2 pa2 ib2 pb2 : BitVec width)
      (m2 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F),
      wordGenGcMoveData conf k (ha, i, pa, ib, pb, old, s.memory, s.mdomain) =
        (i2, pa2, ib2, pb2, m2, true) →
      s.store.lookup .currHeap = some (.word old) → s.useStore = true →
      (s.store.lookup (.temp 0)).isSome = true → (s.store.lookup (.temp 1)).isSome = true →
      s.store.lookup (.temp 2) = some (.word pb) → s.store.lookup (.temp 3) = some (.word ib) →
      (s.regs.lookup 0).isSome = true → (s.regs.lookup 1).isSome = true →
      (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      (s.regs.lookup 7).isSome = true → s.regs.lookup 8 = some (.word ha) →
      ∃ ck r0 r1 r2 r5 r6 r7 t0 t1,
        evaluate (wordGenGcMoveDataCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m2
            store := s.store.updateListEq [(.temp 0, t0), (.temp 1, t1), (.temp 2, .word pb2),
              (.temp 3, .word ib2)]
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa2),
              (4, .word i2), (5, r5), (6, r6), (7, r7), (8, .word pa2)] }) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro ha i pa ib pb i2 pa2 ib2 pb2 m2 s hm hcurr huse ht0 ht1 ht2 ht3 h0 h1 h2 h3 h4 h5 h6 h7
    h8
  rw [wordGenGcMoveData] at hm
  by_cases hp : ha = pa
  · subst hp
    simp only [if_true, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := hm
    obtain ⟨t0, hrt0⟩ := Option.isSome_iff_exists.1 ht0
    obtain ⟨t1, hrt1⟩ := Option.isSome_iff_exists.1 ht1
    obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.1 h0
    obtain ⟨r1, hr1⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨r2, hr2⟩ := Option.isSome_iff_exists.1 h2
    obtain ⟨r5, hr5⟩ := Option.isSome_iff_exists.1 h5
    obtain ⟨r6, hr6⟩ := Option.isSome_iff_exists.1 h6
    obtain ⟨r7, hr7⟩ := Option.isSome_iff_exists.1 h7
    refine ⟨0, r0, r1, r2, r5, r6, r7, t0, t1, ?_⟩
    rw [genGcMove_skip_store s t0 t1 _ _ hrt0 hrt1 ht2 ht3]
    rw [wordGenGcMoveDataCode_eq, evaluate_loop, evaluate_ite, evaluate_break]
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
  have hpb : (!(pa == ha)) = true := by simpa using Ne.symm hp
  by_cases hb : (wordSemTheWord (s.memory ha)).getLsbD 2 = true
  · simp only [hb, if_true] at hm
    generalize hrec : wordGenGcMoveData conf (k - 1) (ha + (decodeLength conf
      (wordSemTheWord (s.memory ha)) + 1) * wordSemBytesInWord, i, pa, ib, pb, old, s.memory,
      s.mdomain) = R at hm
    obtain ⟨i3, pa3, ib3, pb3, m3, c3⟩ := R
    simp only [Prod.mk.injEq, Bool.and_eq_true] at hm
    obtain ⟨rfl, rfl, rfl, rfl, rfl, ⟨hdm, hisw⟩, rfl⟩ := hm
    obtain ⟨x, hx⟩ := (isWord_thm _).1 hisw
    rw [hx] at hrec hb
    simp only [wordSemTheWord] at hrec hb
    let s5 : StackSemStateFiniteExact width C F :=
      setVar 8 (.word (ha + (decodeLength conf x + 1) * wordSemBytesInWord))
        (setVar 7 (.word ((decodeLength conf x + 1) * wordSemBytesInWord)) s)
    obtain ⟨ck, r0, r1, r2, r5, r6, r7, u0, u1, hr⟩ := ih (k - 1) (by omega) _ i pa ib pb i3 pa3
      ib3 pb3 m3 s5 hrec hcurr huse ht0 ht1 ht2 ht3
      (by simpa [s5, setVar, FUPDATE_HOL] using h0) (by simpa [s5, setVar, FUPDATE_HOL] using h1)
      (by simpa [s5, setVar, FUPDATE_HOL] using h2) (by simp [s5, setVar, FUPDATE_HOL, h3])
      (by simp [s5, setVar, FUPDATE_HOL, h4]) (by simpa [s5, setVar, FUPDATE_HOL] using h5)
      (by simpa [s5, setVar, FUPDATE_HOL] using h6) (by simp [s5, setVar, FUPDATE_HOL])
      (by simp [s5, setVar, FUPDATE_HOL])
    refine ⟨ck + 1, r0, r1, r2, r5, r6, r7, u0, u1, ?_⟩
    rw [wordGenGcMoveDataCode_eq, evaluate_loop, evaluate_ite]
    simp only [getVar, HolRegImm.toWordRegImm, h3, StackSemStateOps.getVarImm, h8,
      wordSemWordCmp, wordCmpHOL, hpb]
    rw [dataBody_skip conf _ { s with clock := s.clock + (ck + 1) } ha x hws hw2 hlen hshift
      h8 hdm hx hb]
    have hck : s.clock + (ck + 1) ≠ 0 := by omega
    simp only [fixClock, setVar, contLoop, Nat.min_self, if_true, hck, if_false, decClock,
      ← wordGenGcMoveDataCode_eq]
    refine (congrArg (fun st => evaluate (wordGenGcMoveDataCode conf, st)) ?_).trans (hr.trans ?_)
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
    generalize hl : wordGenGcMoveList conf (ha + wordSemBytesInWord,
      decodeLength conf (wordSemTheWord (s.memory ha)), i, pa, ib, pb, old, s.memory,
      s.mdomain) = R at hm
    obtain ⟨ha3, i1, pa1, ib1, pb1, m1, c1⟩ := R
    simp only at hm
    generalize hrec : wordGenGcMoveData conf (k - 1) (ha3, i1, pa1, ib1, pb1, old, m1,
      s.mdomain) = R2 at hm
    obtain ⟨i3, pa3, ib3, pb3, m3, c3⟩ := R2
    simp only [Prod.mk.injEq, Bool.and_eq_true] at hm
    obtain ⟨rfl, rfl, rfl, rfl, rfl, ⟨hdm, hisw⟩, rfl, rfl⟩ := hm
    obtain ⟨x, hx⟩ := (isWord_thm _).1 hisw
    rw [hx] at hb hl
    simp only [wordSemTheWord] at hb hl
    have hb' : x.getLsbD 2 = false := by simpa using hb
    let s5 : StackSemStateFiniteExact width C F :=
      setVar 8 (.word (ha + wordSemBytesInWord)) (setVar 7 (.word (decodeLength conf x)) s)
    obtain ⟨ck, q0, q1, q2, q5, q6, g0, g1, hL⟩ := word_gen_gc_move_list_code_thm
      (decodeLength conf x) (ha + wordSemBytesInWord) s5 pa1 pa old m1 s.memory i1 i s.mdomain
      conf ha3 ib ib1 pb pb1
      ⟨hl, hsl, hws, hw2, hlen, hshift, hcurr, huse, rfl, rfl, ht0, ht1, ht2, ht3,
        by simpa [s5, setVar, FUPDATE_HOL] using h0, by simpa [s5, setVar, FUPDATE_HOL] using h1,
        by simpa [s5, setVar, FUPDATE_HOL] using h2, by simp [s5, getVar, setVar, FUPDATE_HOL, h3],
        by simp [s5, getVar, setVar, FUPDATE_HOL, h4], by simpa [s5, setVar, FUPDATE_HOL] using h5⟩
      (by simpa [s5, setVar, FUPDATE_HOL] using h6)
      ⟨by simp [s5, getVar, setVar, FUPDATE_HOL], by simp [s5, getVar, setVar, FUPDATE_HOL]⟩
    let s6 : StackSemStateFiniteExact width C F :=
      { s5 with
        memory := m1
        store := s5.store.updateListEq [(.temp 0, g0), (.temp 1, g1), (.temp 2, .word pb1),
          (.temp 3, .word ib1)]
        regs := s5.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa1),
          (4, .word i1), (5, q5), (6, q6), (7, .word 0), (8, .word ha3)] }
    obtain ⟨ck', r0, r1, r2, r5, r6, r7, u0, u1, hr⟩ := ih (k - 1) (by omega) ha3 i1 pa1 ib1 pb1
      i3 pa3 ib3 pb3 m3 s6 hrec
      (by simp [s6, s5, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL,
        FUPDATE_HOL, hcurr])
      huse
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    refine ⟨ck + ck' + 1, r0, r1, r2, r5, r6, r7, u0, u1, ?_⟩
    have hadd := StackProps.evaluateAddClock (ck' + 1) _ _ _ _ ⟨hL, by simp⟩
    have hs5 : setVar 8 (.word (ha + wordSemBytesInWord)) (setVar 7 (.word (decodeLength conf x))
        { s with clock := s.clock + (ck + ck' + 1) }) =
        { { s5 with clock := s5.clock + ck } with
          clock := { s5 with clock := s5.clock + ck }.clock + (ck' + 1) } := by
      simp only [s5, setVar]
      congr 1
      omega
    rw [wordGenGcMoveDataCode_eq, evaluate_loop, evaluate_ite]
    simp only [getVar, HolRegImm.toWordRegImm, h3, StackSemStateOps.getVarImm, h8,
      wordSemWordCmp, wordCmpHOL, hpb]
    rw [dataBody_list conf _ { s with clock := s.clock + (ck + ck' + 1) } ha x hw2 hlen
      h8 hdm hx hb', hs5, hadd]
    have hs5c : s5.clock = s.clock := rfl
    have hmin : min (s.clock + (ck + ck' + 1)) (s5.clock + (ck' + 1)) = s5.clock + (ck' + 1) := by
      omega
    have hck : s5.clock + (ck' + 1) ≠ 0 := by omega
    simp only [fixClock, contLoop, hmin, if_true, hck, if_false, decClock,
      ← wordGenGcMoveDataCode_eq]
    refine (congrArg (fun st => evaluate (wordGenGcMoveDataCode conf, st)) ?_).trans (hr.trans ?_)
    · congr 1
    · simp only [s6, s5, setVar, Prod.mk.injEq, true_and]
      rw [temps_updateListEq_twice]
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

namespace GenGcMoveDataSupport

/-- Canonical finite-support codec of the owning StackSem state carrier, required
by the `fmap_as_finite_support` qualifier of `word_gen_gc_move_data_code_thm`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

end GenGcMoveDataSupport

/-- Exact HOL `word_gen_gc_move_data_code_thm` (`stack_allocProofScript.sml:3992-4122`,
`[local]` in HOL), with HOL's binder order and its four curried premise groups;
HOL's free `conf` is implicit. HOL's `c1`, which the definition call never
mentions, is kept as a quantified Boolean with its premise `c1`, and HOL's
`conf.len_size + 2 < dimindex` premise is retained although this proof does not
use it. `FLOOKUP s.store`, `k IN FDOM`, `|++` and `get_var` are the canonical
carrier's lookups, `updateListEq` and `getVar`, and `Temp nw` is
`WordStore.temp n`; the existentials `ck r0 r1 r2 r5 r6 r7 t0 t1` are kept. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml"
  "word_gen_gc_move_data_code_thm"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_gen_gc_move_data_code_thm {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} :
    ∀ (k : Nat) (ha1 i1 pa1 ib1 pb1 old1 : BitVec width) (m1 : BitVec width → WordLocW width)
      (dm1 : BitVec width → Bool) (c1 : Bool) (i2 pa2 ib2 pb2 : BitVec width)
      (m2 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F),
      wordGenGcMoveData conf k (ha1, i1, pa1, ib1, pb1, old1, m1, dm1) =
          (i2, pa2, ib2, pb2, m2, true) ∧
        shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
        conf.lenSize ≠ 0 ∧ conf.lenSize + 2 < width ∧
        (∀ w : BitVec width, w <<< wordShiftAmount width = w * wordSemBytesInWord) ∧
        s.store.lookup .currHeap = some (.word old1) ∧ s.useStore = true ∧
        s.memory = m1 ∧ s.mdomain = dm1 ∧
        (s.store.lookup (.temp 0)).isSome = true ∧ (s.store.lookup (.temp 1)).isSome = true ∧
        s.store.lookup (.temp 2) = some (.word pb1) ∧ s.store.lookup (.temp 3) = some (.word ib1) ∧
        (s.regs.lookup 0).isSome = true ∧ (s.regs.lookup 1).isSome = true ∧
        (s.regs.lookup 2).isSome = true ∧
        getVar 3 s = some (.word pa1) ∧ getVar 4 s = some (.word i1) ∧
        (s.regs.lookup 5).isSome = true →
      (s.regs.lookup 6).isSome = true →
      (s.regs.lookup 7).isSome = true →
      getVar 8 s = some (.word ha1) ∧ c1 = true →
      ∃ ck r0 r1 r2 r5 r6 r7 t0 t1,
        evaluate (wordGenGcMoveDataCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m2
            store := s.store.updateListEq [(.temp 0, t0), (.temp 1, t1), (.temp 2, .word pb2),
              (.temp 3, .word ib2)]
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa2),
              (4, .word i2), (5, r5), (6, r6), (7, r7), (8, .word pa2)] }) := by
  rintro k ha1 i1 pa1 ib1 pb1 old1 m1 dm1 c1 i2 pa2 ib2 pb2 m2 s
    ⟨hm, hsl, hws, hw2, hlen, -, hshift, hcurr, huse, rfl, rfl, ht0, ht1, ht2, ht3, h0, h1, h2,
      h3, h4, h5⟩ h6 h7 ⟨h8, -⟩
  exact wordGenGcMoveDataCode_run hsl hws hw2 hlen hshift old1 k ha1 i1 pa1 ib1 pb1 i2 pa2 ib2
    pb2 m2 s hm hcurr huse ht0 ht1 ht2 ht3 h0 h1 h2 (by simpa [getVar] using h3)
    (by simpa [getVar] using h4) h5 h6 h7 (by simpa [getVar] using h8)

end Flapjack.Compiler.Backend.StackAlloc
