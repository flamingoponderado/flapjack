import Mathlib.Data.Nat.Basic
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GcMoveList
import Flapjack.Compiler.Backend.StackAlloc.Proofs.Unroll

/-!
# `stack_allocProof` `word_gc_move_bitmap_code_thm`

`word_gc_move_bitmap_code_thm` of
`cakeml/compiler/backend/proofs/stack_allocProofScript.sml` (1166-1311): the
stackLang `word_gc_move_bitmap_code` loop run by the exact StackSem `evaluate`
simulates the shallow `word_gcFunctions` `word_gc_move_bitmap` on the stack
slots after `init ++ old`. As in HOL, the proof is an induction on the bitmap
word (`bit_length_ind`, here on its value); each set bit moves one slot by
`word_gc_move_code_thm`, composed with the induction hypothesis through
`evaluate_add_clock`. The stack-instruction evaluation lemmas are Flapjack
infrastructure.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackRemove (loadInst storeInst leftShiftInst rightShiftInst)

/-- A stack offset `j` in bytes, `bytes_in_word * n2w j`, shifts back to `j`. -/
theorem stackOffset_shift {width : Nat} [NeZero width] (j : Nat) (hg : goodDimindex width)
    (hb : (width / 8) * j < 2 ^ width) :
    (wordSemBytesInWord * BitVec.ofNat width j) >>> wordShiftAmount width = BitVec.ofNat width j ∧
      (BitVec.ofNat width j).toNat = j ∧
      (BitVec.ofNat width j) <<< wordShiftAmount width = wordSemBytesInWord * BitVec.ofNat width j := by
  refine ⟨bytesInWord_wordShift_n2w ⟨hg, hb⟩, ?_, (bytesInWord_mul_eq_shift _ hg).symm⟩
  have h8 : 1 ≤ width / 8 := by rcases hg with rfl | rfl <;> decide
  have : j < 2 ^ width := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left j h8) hb
  simp [Nat.mod_eq_of_lt this]

theorem stackLoadAny_eval {width : Nat} [NeZero width] {C F : Type}
    (S : StackSemStateFiniteExact width C F) (r rn j : Nat) (hu : S.useStack = true)
    (h : S.regs.lookup rn = some (.word (wordSemBytesInWord * BitVec.ofNat width j)))
    (hg : goodDimindex width) (hb : (width / 8) * j < 2 ^ width)
    (hj : S.stackSpace + j < S.stack.length) :
    evaluate (.stackLoadAny r rn, S) = (none, setVar r S.stack[S.stackSpace + j] S) := by
  obtain ⟨hsh, hjn, hback⟩ := stackOffset_shift j hg hb
  rw [evaluate_stackLoadAny]
  simp [hu, getVar, h, hsh, hjn, hback, hj]

theorem stackStoreAny_eval {width : Nat} [NeZero width] {C F : Type}
    (S : StackSemStateFiniteExact width C F) (r rn j : Nat) (v : WordLocW width)
    (hu : S.useStack = true) (hv : S.regs.lookup r = some v)
    (h : S.regs.lookup rn = some (.word (wordSemBytesInWord * BitVec.ofNat width j)))
    (hg : goodDimindex width) (hb : (width / 8) * j < 2 ^ width)
    (hj : S.stackSpace + j < S.stack.length) :
    evaluate (.stackStoreAny r rn, S) =
      (none, { S with stack := S.stack.set (S.stackSpace + j) v }) := by
  obtain ⟨hsh, hjn, hback⟩ := stackOffset_shift j hg hb
  rw [evaluate_stackStoreAny]
  simp [hu, getVar, hv, h, hsh, hjn, hback, hj]

/-- The `word_gc_move_bitmap_code` loop entry: the `While` test on register 7. -/
theorem wordGcMoveBitmapCode_eq {width : Nat} [NeZero width] (conf : Config) :
    (wordGcMoveBitmapCode conf : HolProg width) =
      .loop (.ite .notLower 7 (.imm 2)
        (.ite .test 7 (.imm 1)
          (.seq (rightShiftInst 7 1) (addBytesInWordInst 8))
          (.seq (.stackLoadAny 5 8) (.seq (rightShiftInst 7 1) (.seq (wordGcMoveCode conf)
            (.seq (.stackStoreAny 5 8) (addBytesInWordInst 8))))))
        (.break 0)) := rfl

/-- One loop body on a clear bitmap bit: skip the slot. -/
theorem gcMoveBitmap_body_skip {width : Nat} [NeZero width] {C F : Type} (conf : Config)
    (S : StackSemStateFiniteExact width C F) (w W : BitVec width) (hw2 : 2 < width)
    (h7 : S.regs.lookup 7 = some (.word w)) (h8 : S.regs.lookup 8 = some (.word W))
    (hb : w &&& 1 = 0) :
    evaluate (.ite .test 7 (.imm 1)
        (.seq (rightShiftInst 7 1) (addBytesInWordInst 8))
        (.seq (.stackLoadAny 5 8) (.seq (rightShiftInst 7 1) (.seq (wordGcMoveCode conf)
          (.seq (.stackStoreAny 5 8) (addBytesInWordInst 8))))), S) =
      (none, setVar 8 (.word (W + wordSemBytesInWord)) (setVar 7 (.word (w >>> (1 : Nat))) S)) := by
  have hpow : width < 2 ^ width := Nat.lt_two_pow_self
  have h1m : 1 % 2 ^ width = 1 := Nat.mod_eq_of_lt (by omega)
  have h1_le : ¬ width ≤ 1 := by omega
  have hbit : (AndOp.and w (1#width) == 0#width) = true := by
    have ha : AndOp.and w (1#width) = 0#width := hb
    simpa using ha
  rw [evaluate_ite]
  simp [getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, wordSemWordCmp,
    wordCmpHOL, evaluate_seq, evaluate_inst, addBytesInWordInst, rightShiftInst,
    StackSemInst.instHOL, StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, setVar, wordOpHOL, wordOp, fixClock,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, h7, h8, hbit, h1m, h1_le, wordShiftHOL]

/-- One loop body on a set bitmap bit, up to `word_gc_move_code`: load the slot
into register 5 and shift the bitmap. -/
theorem gcMoveBitmap_body_move {width : Nat} [NeZero width] {C F : Type} (conf : Config)
    (S : StackSemStateFiniteExact width C F) (w : BitVec width) (j : Nat) (hw2 : 2 < width)
    (hu : S.useStack = true) (h7 : S.regs.lookup 7 = some (.word w))
    (h8 : S.regs.lookup 8 = some (.word (wordSemBytesInWord * BitVec.ofNat width j)))
    (hg : goodDimindex width) (hbj : (width / 8) * j < 2 ^ width)
    (hj : S.stackSpace + j < S.stack.length) (v : WordLocW width)
    (hv : S.stack[S.stackSpace + j] = v) (hb : ¬ w &&& 1 = 0) :
    evaluate (.ite .test 7 (.imm 1)
        (.seq (rightShiftInst 7 1) (addBytesInWordInst 8))
        (.seq (.stackLoadAny 5 8) (.seq (rightShiftInst 7 1) (.seq (wordGcMoveCode conf)
          (.seq (.stackStoreAny 5 8) (addBytesInWordInst 8))))), S) =
      evaluate (.seq (wordGcMoveCode conf) (.seq (.stackStoreAny 5 8) (addBytesInWordInst 8)),
        setVar 7 (.word (w >>> (1 : Nat))) (setVar 5 v S)) := by
  have hpow : width < 2 ^ width := Nat.lt_two_pow_self
  have h1m : 1 % 2 ^ width = 1 := Nat.mod_eq_of_lt (by omega)
  have h1_le : ¬ width ≤ 1 := by omega
  have hbit : (AndOp.and w (1#width) == 0#width) = false := by
    have ha : ¬ AndOp.and w (1#width) = 0#width := hb
    simpa using ha
  rw [evaluate_ite]
  simp [getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, wordSemWordCmp,
    wordCmpHOL, h7, hbit]
  have hsh : evaluate (rightShiftInst 7 1, setVar 5 v S) =
      (none, setVar 7 (.word (w >>> (1 : Nat))) (setVar 5 v S)) := by
    simp [evaluate_inst, rightShiftInst, StackSemInst.instHOL,
      StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
      StackSemExpressions.wordExp, setVar,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, h7, h1m, h1_le, wordShiftHOL]
  rw [evaluate_seq_none _ _ _ _ (stackLoadAny_eval S 5 8 j hu h8 hg hbj hj) (by simp only [setVar]; exact Nat.le_refl _), hv,
    evaluate_seq_none _ _ _ _ hsh (by simp only [setVar]; exact Nat.le_refl _)]

/-- HOL's `bit_length_ind` induction, on the bitmap word's value, with the source
hypotheses. -/
theorem wordGcMoveBitmapCode_run {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord)
    (init : List (WordLocW width)) :
    ∀ (n : Nat) (w : BitVec width), w.toNat = n →
    ∀ (stack old new stack1 : List (WordLocW width)) (i pa curr i1 pa1 : BitVec width)
      (m1 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F),
      wordGcMoveBitmap conf (w, stack, i, pa, curr, s.memory, s.mdomain) =
        some (new, stack1, i1, pa1, m1, true) →
      s.store.lookup .currHeap = some (.word curr) → s.useStore = true → s.useStack = true →
      (s.regs.lookup 0).isSome = true → (s.regs.lookup 1).isSome = true →
      (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      s.regs.lookup 7 = some (.word w) →
      s.regs.lookup 8 = some (.word (wordSemBytesInWord * BitVec.ofNat width old.length)) →
      s.stack = init ++ old ++ stack → s.stackSpace = init.length →
      (width / 8) * s.stack.length < 2 ^ width →
      ∃ ck r0 r1 r2 r5 r6 r7,
        evaluate (wordGcMoveBitmapCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m1
            stack := init ++ old ++ new ++ stack1
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
              (4, .word i1), (5, r5), (6, r6), (7, r7),
              (8, .word (wordSemBytesInWord * BitVec.ofNat width (old ++ new).length))] }) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hwn stack old new stack1 i pa curr i1 pa1 m1 s hm hcurr huse hus h0 h1 h2 h3 h4 h5 h6
    h7 h8 hst hsp hbound
  rw [wordGcMoveBitmap_unroll] at hm
  by_cases hlow : w = 0 ∨ w = 1
  · have hm' : some ([], stack, i, pa, s.memory, true) =
        some (new, stack1, i1, pa1, m1, true) := by
      rcases hlow with rfl | rfl
      · simpa using hm
      · simpa using hm
    simp only [Option.some.injEq, Prod.mk.injEq] at hm'
    obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := hm'
    have hlt : w < 2#width := (lower_2w_eq w hg).2 hlow
    obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.1 h0
    obtain ⟨r1, hr1⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨r2, hr2⟩ := Option.isSome_iff_exists.1 h2
    obtain ⟨r5, hr5⟩ := Option.isSome_iff_exists.1 h5
    obtain ⟨r6, hr6⟩ := Option.isSome_iff_exists.1 h6
    refine ⟨0, r0, r1, r2, r5, r6, .word w, ?_⟩
    rw [wordGcMoveBitmapCode_eq, evaluate_loop, evaluate_ite, evaluate_break]
    simp only [getVar, HolRegImm.toWordRegImm, Nat.add_zero, h7]
    simp [StackSemStateOps.getVarImm, wordSemWordCmp, wordCmpHOL, fixClock, contLoop,
      StackSemControl.exitLoop, hlt, hst]
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
    · subst k7; simp [h7]
    by_cases k8 : k = 8
    · subst k8; simp [h8]
    simp [k0, k1, k2, k3, k4, k5, k6, k7, k8]
  have hw0 : w ≠ 0 := fun h => hlow (Or.inl h)
  have hw1 : w ≠ 1 := fun h => hlow (Or.inr h)
  have hnlt : ¬ w < 2#width := fun h => hlow ((lower_2w_eq w hg).1 h)
  have hlt' : (w >>> (1 : Nat)).toNat < n := by
    rw [← hwn, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have : w.toNat ≠ 0 := fun h => hw0 (BitVec.eq_of_toNat_eq (by simpa using h))
    omega
  simp only [hw0, hw1, if_false] at hm
  cases stack with
  | nil => simp at hm
  | cons x xs =>
  have hlen_le : (width / 8) * old.length < 2 ^ width :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (by simp [hst]; omega)) hbound
  have hj : s.stackSpace + old.length < s.stack.length := by simp [hst, hsp]
  have hB : ∀ y : WordLocW width, wordSemBytesInWord * BitVec.ofNat width old.length +
      wordSemBytesInWord = wordSemBytesInWord * BitVec.ofNat width (old ++ [y]).length := by
    intro y
    simp [List.length_append, BitVec.ofNat_add, BitVec.mul_add]
  have hnlt' : (!decide (w < (2 : BitVec width))) = true := by simpa using hnlt
  by_cases hb : w &&& 1 = 0
  · simp only [hb, if_true] at hm
    generalize hrec : wordGcMoveBitmap conf (w >>> (1 : Nat), xs, i, pa, curr, s.memory,
      s.mdomain) = R at hm
    rcases R with _ | ⟨new', st', i', pa', m', c'⟩
    · simp at hm
    simp only [Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hm
    let s2 : StackSemStateFiniteExact width C F :=
      setVar 8 (.word (wordSemBytesInWord * BitVec.ofNat width (old ++ [x]).length))
        (setVar 7 (.word (w >>> (1 : Nat))) s)
    obtain ⟨ck, r0, r1, r2, r5, r6, r7, hr⟩ := ih _ hlt' (w >>> (1 : Nat)) rfl xs (old ++ [x])
      new' st' i pa curr i' pa' m' s2 hrec hcurr huse hus
      (by simpa [s2, setVar, FUPDATE_HOL] using h0) (by simpa [s2, setVar, FUPDATE_HOL] using h1)
      (by simpa [s2, setVar, FUPDATE_HOL] using h2) (by simp [s2, setVar, FUPDATE_HOL, h3])
      (by simp [s2, setVar, FUPDATE_HOL, h4]) (by simpa [s2, setVar, FUPDATE_HOL] using h5)
      (by simpa [s2, setVar, FUPDATE_HOL] using h6) (by simp [s2, setVar, FUPDATE_HOL])
      (by simp [s2, setVar, FUPDATE_HOL]) (by simp [s2, setVar, hst]) hsp
      (by simpa [s2, setVar] using hbound)
    refine ⟨ck + 1, r0, r1, r2, r5, r6, r7, ?_⟩
    rw [wordGcMoveBitmapCode_eq, evaluate_loop, evaluate_ite]
    simp only [getVar, HolRegImm.toWordRegImm, h7, StackSemStateOps.getVarImm, wordSemWordCmp,
      wordCmpHOL, hnlt']
    rw [gcMoveBitmap_body_skip conf { s with clock := s.clock + (ck + 1) } w _ hw2 h7 h8 hb]
    have hck : s.clock + (ck + 1) ≠ 0 := by omega
    simp only [fixClock, setVar, contLoop, Nat.min_self, if_true, hck, if_false, decClock,
      ← wordGcMoveBitmapCode_eq]
    refine (congrArg (fun st => evaluate (wordGcMoveBitmapCode conf, st)) ?_).trans (hr.trans ?_)
    · simp only [s2, setVar, hB x]
      congr 1
    · simp only [s2, setVar, Prod.mk.injEq, true_and]
      congr 1
      · apply regs_ext
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
      · simp
  · simp only [hb, if_false] at hm
    generalize hmv : wordGcMove conf (x, i, pa, curr, s.memory, s.mdomain) = R1 at hm
    obtain ⟨x1, i', pa', m', c1⟩ := R1
    simp only at hm
    generalize hrec : wordGcMoveBitmap conf (w >>> (1 : Nat), xs, i', pa', curr, m',
      s.mdomain) = R at hm
    rcases R with _ | ⟨new', st', i'', pa'', m'', c'⟩
    · simp at hm
    simp only [Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true] at hm
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hm
    -- the state entering `word_gc_move_code`
    let s4 : StackSemStateFiniteExact width C F := setVar 7 (.word (w >>> (1 : Nat))) (setVar 5 x s)
    obtain ⟨ck, q0, q1, q2, q6, hgc⟩ := word_gc_move_code_thm (s := s4)
      ⟨hmv, hsl, hws, hw2, hlen, hshift, hcurr, huse, rfl, rfl,
        by simpa [s4, setVar, FUPDATE_HOL] using h0, by simpa [s4, setVar, FUPDATE_HOL] using h1,
        by simpa [s4, setVar, FUPDATE_HOL] using h2, by simp [s4, getVar, setVar, FUPDATE_HOL, h3],
        by simp [s4, getVar, setVar, FUPDATE_HOL, h4], by simp [s4, getVar, setVar, FUPDATE_HOL],
        by simpa [s4, setVar, FUPDATE_HOL] using h6⟩
    -- the state the next iteration starts from
    let s5 : StackSemStateFiniteExact width C F :=
      setVar 8 (.word (wordSemBytesInWord * BitVec.ofNat width (old ++ [x1]).length))
        { s4 with
          memory := m'
          stack := init ++ old ++ [x1] ++ xs
          regs := s4.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa'),
            (4, .word i'), (5, x1), (6, q6)] }
    obtain ⟨ck', r0, r1, r2, r5, r6, r7, hr⟩ := ih _ hlt' (w >>> (1 : Nat)) rfl xs (old ++ [x1])
      new' st' i' pa' curr i'' pa'' m'' s5 hrec hcurr huse hus
      (by simp [s5, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [s5, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [s5, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [s5, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [s5, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [s5, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [s5, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [s5, s4, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq,
        FUPDATE_LIST_HOL])
      (by simp [s5, setVar, FUPDATE_HOL]) (by simp [s5, setVar]) hsp
      (by simpa [s5, s4, setVar, hst] using hbound)
    refine ⟨ck + ck' + 1, r0, r1, r2, r5, r6, r7, ?_⟩
    have hadd := StackProps.evaluateAddClock (ck' + 1) _ _ _ _ ⟨hgc, by simp⟩
    have hs4 : setVar 7 (.word (w >>> (1 : Nat))) (setVar 5 x
        { s with clock := s.clock + (ck + ck' + 1) }) =
        { { s4 with clock := s4.clock + ck } with
          clock := { s4 with clock := s4.clock + ck }.clock + (ck' + 1) } := by
      simp only [s4, setVar]
      congr 1
      omega
    have hv : ({ s with clock := s.clock + (ck + ck' + 1) } :
        StackSemStateFiniteExact width C F).stack[s.stackSpace + old.length]'hj = x := by
      simp [hst, hsp]
    rw [wordGcMoveBitmapCode_eq, evaluate_loop, evaluate_ite]
    simp only [getVar, HolRegImm.toWordRegImm, h7, StackSemStateOps.getVarImm, wordSemWordCmp,
      wordCmpHOL, hnlt']
    rw [gcMoveBitmap_body_move conf { s with clock := s.clock + (ck + ck' + 1) } w old.length hw2
      hus h7 h8 hg hlen_le hj x hv hb, hs4,
      evaluate_seq_none _ _ _ _ hadd (by simp [s4, setVar]),
      evaluate_seq_none _ _ _ _ (stackStoreAny_eval _ 5 8 old.length x1 ?_ ?_ ?_ hg hlen_le ?_)
        (by exact Nat.le_refl _),
      addBytesInWordInst_eval _ 8 (wordSemBytesInWord * BitVec.ofNat width old.length) ?_]
    all_goals first
      | exact hus
      | (simpa [s4, setVar] using hj)
      | (simp [s4, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL,
          h8]; done)
      | skip
    have hs4c : s4.clock = s.clock := rfl
    have hmin : min (s.clock + (ck + ck' + 1)) (s4.clock + (ck' + 1)) = s4.clock + (ck' + 1) := by
      omega
    have hck : s4.clock + (ck' + 1) ≠ 0 := by omega
    simp only [fixClock, setVar, contLoop, hmin, if_true, hck, if_false, decClock,
      ← wordGcMoveBitmapCode_eq]
    refine (congrArg (fun st => evaluate (wordGcMoveBitmapCode conf, st)) ?_).trans (hr.trans ?_)
    · simp only [s5, s4, setVar, hB x1, hsp, hst]
      congr 1
      simp
    · simp only [s5, s4, setVar, Prod.mk.injEq, true_and]
      congr 1
      · apply regs_ext
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
      · simp

namespace GcMoveBitmapSupport

/-- Canonical finite-support codec of the owning StackSem state carrier, required
by the `fmap_as_finite_support` qualifier of `word_gc_move_bitmap_code_thm`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

end GcMoveBitmapSupport

/-- Exact HOL `word_gc_move_bitmap_code_thm` (`stack_allocProofScript.sml:1166-1311`),
with HOL's binder order; HOL's free `conf` and `init` are implicit, and its
quantified `a1`, which the statement never mentions, is kept. `FLOOKUP s.store
CurrHeap`, `k IN FDOM s.regs`, `|++` and `get_var` are the canonical carrier's
lookups, `updateListEq` and `getVar`; `dimindex (:'a) DIV 8` and `dimword (:'a)`
are `width / 8` and `2 ^ width`; the existentials `ck r0 r1 r2 r5 r6 r7` are kept. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem word_gc_move_bitmap_code_thm {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    {init : List (WordLocW width)} :
    ∀ (w : BitVec width) (stack : List (WordLocW width)) (s : StackSemStateFiniteExact width C F)
      (i pa curr : BitVec width) (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
      (new stack1 : List (WordLocW width)) (_a1 i1 pa1 : BitVec width)
      (m1 : BitVec width → WordLocW width) (old : List (WordLocW width)),
      wordGcMoveBitmap conf (w, stack, i, pa, curr, m, dm) =
          some (new, stack1, i1, pa1, m1, true) ∧
        shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
        conf.lenSize ≠ 0 ∧ goodDimindex width ∧
        (∀ w : BitVec width, w <<< wordShiftAmount width = w * wordSemBytesInWord) ∧
        s.store.lookup .currHeap = some (.word curr) ∧ s.useStore = true ∧
        s.memory = m ∧ s.mdomain = dm ∧ s.useStack = true ∧
        (s.regs.lookup 0).isSome = true ∧ (s.regs.lookup 1).isSome = true ∧
        (s.regs.lookup 2).isSome = true ∧
        getVar 3 s = some (.word pa) ∧ getVar 4 s = some (.word i) ∧
        (s.regs.lookup 5).isSome = true ∧ (s.regs.lookup 6).isSome = true ∧
        getVar 7 s = some (.word w) ∧
        getVar 8 s = some (.word (wordSemBytesInWord * BitVec.ofNat width old.length)) ∧
        s.stack = init ++ old ++ stack ∧ s.stackSpace = init.length ∧
        (width / 8) * s.stack.length < 2 ^ width →
      ∃ ck r0 r1 r2 r5 r6 r7,
        evaluate (wordGcMoveBitmapCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m1
            stack := init ++ old ++ new ++ stack1
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
              (4, .word i1), (5, r5), (6, r6), (7, r7),
              (8, .word (wordSemBytesInWord * BitVec.ofNat width (old ++ new).length))] }) := by
  rintro w stack s i pa curr m dm new stack1 _ i1 pa1 m1 old
    ⟨hm, hsl, hws, hw2, hlen, hg, hshift, hcurr, huse, rfl, rfl, hus, h0, h1, h2, h3, h4, h5, h6,
      h7, h8, hst, hsp, hbound⟩
  exact wordGcMoveBitmapCode_run hsl hws hw2 hlen hg hshift init w.toNat w rfl stack old new
    stack1 i pa curr i1 pa1 m1 s hm hcurr huse hus h0 h1 h2 (by simpa [getVar] using h3)
    (by simpa [getVar] using h4) h5 h6 (by simpa [getVar] using h7) (by simpa [getVar] using h8)
    hst hsp hbound

end Flapjack.Compiler.Backend.StackAlloc
