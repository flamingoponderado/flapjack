import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GcMoveBitmap
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenGcMove

/-!
# `stack_allocProof` `word_gen_gc_move_bitmap_code_thm`

`word_gen_gc_move_bitmap_code_thm` of
`cakeml/compiler/backend/proofs/stack_allocProofScript.sml` (2805-2976): the
generational counterpart of `word_gc_move_bitmap_code_thm`. The stackLang
`word_gen_gc_move_bitmap_code` loop run by the exact StackSem `evaluate`
simulates `word_gen_gc_move_bitmap`; each set bit moves one stack slot by
`word_gen_gc_move_code_thm`, composed with the induction hypothesis through
`evaluate_add_clock`, and the `Temp 0w`-`Temp 3w` store slots are threaded.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackRemove (loadInst storeInst leftShiftInst rightShiftInst)

/-- The `word_gen_gc_move_bitmap_code` loop entry: the `While` test on register 7. -/
theorem wordGenGcMoveBitmapCode_eq {width : Nat} [NeZero width] (conf : Config) :
    (wordGenGcMoveBitmapCode conf : HolProg width) =
      .loop (.ite .notLower 7 (.imm 2)
        (.ite .test 7 (.imm 1)
          (.seq (rightShiftInst 7 1) (addBytesInWordInst 8))
          (.seq (.stackLoadAny 5 8) (.seq (rightShiftInst 7 1) (.seq (wordGenGcMoveCode conf)
            (.seq (.stackStoreAny 5 8) (addBytesInWordInst 8))))))
        (.break 0)) := rfl

/-- One bitmap-loop body on a clear bit, for any slot-moving program `G`. -/
theorem bitmapBody_skip {width : Nat} [NeZero width] {C F : Type} (G : HolProg width)
    (S : StackSemStateFiniteExact width C F) (w W : BitVec width) (hw2 : 2 < width)
    (h7 : S.regs.lookup 7 = some (.word w)) (h8 : S.regs.lookup 8 = some (.word W))
    (hb : w &&& 1 = 0) :
    evaluate (.ite .test 7 (.imm 1)
        (.seq (rightShiftInst 7 1) (addBytesInWordInst 8))
        (.seq (.stackLoadAny 5 8) (.seq (rightShiftInst 7 1) (.seq G
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

/-- One bitmap-loop body on a set bit, up to the slot-moving program `G`. -/
theorem bitmapBody_move {width : Nat} [NeZero width] {C F : Type} (G : HolProg width)
    (S : StackSemStateFiniteExact width C F) (w : BitVec width) (j : Nat) (hw2 : 2 < width)
    (hu : S.useStack = true) (h7 : S.regs.lookup 7 = some (.word w))
    (h8 : S.regs.lookup 8 = some (.word (wordSemBytesInWord * BitVec.ofNat width j)))
    (hg : goodDimindex width) (hbj : (width / 8) * j < 2 ^ width)
    (hj : S.stackSpace + j < S.stack.length) (v : WordLocW width)
    (hv : S.stack[S.stackSpace + j] = v) (hb : ¬ w &&& 1 = 0) :
    evaluate (.ite .test 7 (.imm 1)
        (.seq (rightShiftInst 7 1) (addBytesInWordInst 8))
        (.seq (.stackLoadAny 5 8) (.seq (rightShiftInst 7 1) (.seq G
          (.seq (.stackStoreAny 5 8) (addBytesInWordInst 8))))), S) =
      evaluate (.seq G (.seq (.stackStoreAny 5 8) (addBytesInWordInst 8)),
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
  rw [evaluate_seq_none _ _ _ _ (stackLoadAny_eval S 5 8 j hu h8 hg hbj hj) le_rfl, hv,
    evaluate_seq_none _ _ _ _ hsh le_rfl]

/-- Later updates of the four `Temp` slots override earlier ones. -/
theorem temps_updateListEq_twice {width : Nat} [NeZero width]
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (a0 a1 a2 a3 b0 b1 b2 b3 : WordLocW width) :
    (st.updateListEq [(.temp 0, a0), (.temp 1, a1), (.temp 2, a2), (.temp 3, a3)]).updateListEq
        [(.temp 0, b0), (.temp 1, b1), (.temp 2, b2), (.temp 3, b3)] =
      st.updateListEq [(.temp 0, b0), (.temp 1, b1), (.temp 2, b2), (.temp 3, b3)] := by
  apply regs_ext
  intro k
  simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl, FUPDATE_HOL]
  by_cases k0 : k = .temp 0
  · subst k0; simp
  by_cases k1 : k = .temp 1
  · subst k1; simp
  by_cases k2 : k = .temp 2
  · subst k2; simp
  by_cases k3 : k = .temp 3
  · subst k3; simp
  simp only [BitVec.ofNat_eq_ofNat] at k0 k1 k2 k3
  simp [k0, k1, k2, k3]

/-- HOL's `bit_length_ind` induction, on the bitmap word's value, with the source
hypotheses. -/
theorem wordGenGcMoveBitmapCode_run {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord)
    (init : List (WordLocW width)) :
    ∀ (n : Nat) (w : BitVec width), w.toNat = n →
    ∀ (stack old new stack1 : List (WordLocW width)) (i pa ib pb curr i1 pa1 ib1 pb1 : BitVec width)
      (m1 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F),
      wordGenGcMoveBitmap conf (w, stack, i, pa, ib, pb, curr, s.memory, s.mdomain) =
        some (new, stack1, i1, pa1, ib1, pb1, m1, true) →
      s.store.lookup .currHeap = some (.word curr) → s.useStore = true → s.useStack = true →
      (s.regs.lookup 0).isSome = true → (s.regs.lookup 1).isSome = true →
      (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      s.regs.lookup 7 = some (.word w) →
      s.regs.lookup 8 = some (.word (wordSemBytesInWord * BitVec.ofNat width old.length)) →
      (s.store.lookup (.temp 0)).isSome = true → (s.store.lookup (.temp 1)).isSome = true →
      s.store.lookup (.temp 2) = some (.word pb) → s.store.lookup (.temp 3) = some (.word ib) →
      s.stack = init ++ old ++ stack → s.stackSpace = init.length →
      (width / 8) * s.stack.length < 2 ^ width →
      ∃ ck r0 r1 r2 r5 r6 r7 t0 t1,
        evaluate (wordGenGcMoveBitmapCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m1
            stack := init ++ old ++ new ++ stack1
            store := s.store.updateListEq [(.temp 0, t0), (.temp 1, t1), (.temp 2, .word pb1),
              (.temp 3, .word ib1)]
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
              (4, .word i1), (5, r5), (6, r6), (7, r7),
              (8, .word (wordSemBytesInWord * BitVec.ofNat width (old ++ new).length))] }) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hwn stack old new stack1 i pa ib pb curr i1 pa1 ib1 pb1 m1 s hm hcurr huse hus h0 h1 h2
    h3 h4 h5 h6 h7 h8 ht0 ht1 ht2 ht3 hst hsp hbound
  obtain ⟨t0, hrt0⟩ := Option.isSome_iff_exists.1 ht0
  obtain ⟨t1, hrt1⟩ := Option.isSome_iff_exists.1 ht1
  rw [wordGenGcMoveBitmap_unroll] at hm
  by_cases hlow : w = 0 ∨ w = 1
  · have hm' : some ([], stack, i, pa, ib, pb, s.memory, true) =
        some (new, stack1, i1, pa1, ib1, pb1, m1, true) := by
      rcases hlow with rfl | rfl
      · simpa using hm
      · simpa using hm
    simp only [Option.some.injEq, Prod.mk.injEq] at hm'
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hm'
    have hlt : w < 2#width := (lower_2w_eq w hg).2 hlow
    obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.1 h0
    obtain ⟨r1, hr1⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨r2, hr2⟩ := Option.isSome_iff_exists.1 h2
    obtain ⟨r5, hr5⟩ := Option.isSome_iff_exists.1 h5
    obtain ⟨r6, hr6⟩ := Option.isSome_iff_exists.1 h6
    refine ⟨0, r0, r1, r2, r5, r6, .word w, t0, t1, ?_⟩
    rw [genGcMove_skip_store s t0 t1 _ _ hrt0 hrt1 ht2 ht3]
    rw [wordGenGcMoveBitmapCode_eq, evaluate_loop, evaluate_ite, evaluate_break]
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
    generalize hrec : wordGenGcMoveBitmap conf (w >>> (1 : Nat), xs, i, pa, ib, pb, curr, s.memory,
      s.mdomain) = R at hm
    rcases R with _ | ⟨new', st', i', pa', ib', pb', m', c'⟩
    · simp at hm
    simp only [Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hm
    let s2 : StackSemStateFiniteExact width C F :=
      setVar 8 (.word (wordSemBytesInWord * BitVec.ofNat width (old ++ [x]).length))
        (setVar 7 (.word (w >>> (1 : Nat))) s)
    obtain ⟨ck, r0, r1, r2, r5, r6, r7, u0, u1, hr⟩ := ih _ hlt' (w >>> (1 : Nat)) rfl xs
      (old ++ [x]) new' st' i pa ib pb curr i' pa' ib' pb' m' s2 hrec hcurr huse hus
      (by simpa [s2, setVar, FUPDATE_HOL] using h0) (by simpa [s2, setVar, FUPDATE_HOL] using h1)
      (by simpa [s2, setVar, FUPDATE_HOL] using h2) (by simp [s2, setVar, FUPDATE_HOL, h3])
      (by simp [s2, setVar, FUPDATE_HOL, h4]) (by simpa [s2, setVar, FUPDATE_HOL] using h5)
      (by simpa [s2, setVar, FUPDATE_HOL] using h6) (by simp [s2, setVar, FUPDATE_HOL])
      (by simp [s2, setVar, FUPDATE_HOL]) ht0 ht1 ht2 ht3 (by simp [s2, setVar, hst]) hsp
      (by simpa [s2, setVar] using hbound)
    refine ⟨ck + 1, r0, r1, r2, r5, r6, r7, u0, u1, ?_⟩
    rw [wordGenGcMoveBitmapCode_eq, evaluate_loop, evaluate_ite]
    simp only [getVar, HolRegImm.toWordRegImm, h7, StackSemStateOps.getVarImm, wordSemWordCmp,
      wordCmpHOL, hnlt']
    rw [bitmapBody_skip _ { s with clock := s.clock + (ck + 1) } w _ hw2 h7 h8 hb]
    have hck : s.clock + (ck + 1) ≠ 0 := by omega
    simp only [fixClock, setVar, contLoop, Nat.min_self, if_true, hck, if_false, decClock,
      ← wordGenGcMoveBitmapCode_eq]
    refine (congrArg (fun st => evaluate (wordGenGcMoveBitmapCode conf, st)) ?_).trans
      (hr.trans ?_)
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
    generalize hmv : wordGenGcMove conf (x, i, pa, ib, pb, curr, s.memory, s.mdomain) = R1 at hm
    obtain ⟨x1, i', pa', ib', pb', m', c1⟩ := R1
    simp only at hm
    generalize hrec : wordGenGcMoveBitmap conf (w >>> (1 : Nat), xs, i', pa', ib', pb', curr, m',
      s.mdomain) = R at hm
    rcases R with _ | ⟨new', st', i'', pa'', ib'', pb'', m'', c'⟩
    · simp at hm
    simp only [Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true] at hm
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hm
    -- the state entering `word_gen_gc_move_code`
    let s4 : StackSemStateFiniteExact width C F := setVar 7 (.word (w >>> (1 : Nat))) (setVar 5 x s)
    obtain ⟨ck, q0, q1, q2, q6, g0, g1, hgc⟩ := word_gen_gc_move_code_thm (s := s4)
      ⟨hmv, hsl, hws, hw2, hlen, hshift, hcurr, huse, rfl, rfl,
        by simpa [s4, setVar, FUPDATE_HOL] using h0, by simpa [s4, setVar, FUPDATE_HOL] using h1,
        by simpa [s4, setVar, FUPDATE_HOL] using h2, by simp [s4, getVar, setVar, FUPDATE_HOL, h3],
        by simp [s4, getVar, setVar, FUPDATE_HOL, h4], by simp [s4, getVar, setVar, FUPDATE_HOL],
        ht0, ht1, ht2, ht3,
        by simpa [s4, setVar, FUPDATE_HOL] using h1, by simpa [s4, setVar, FUPDATE_HOL] using h2,
        by simpa [s4, setVar, FUPDATE_HOL] using h6⟩
    -- the state the next iteration starts from
    let s5 : StackSemStateFiniteExact width C F :=
      setVar 8 (.word (wordSemBytesInWord * BitVec.ofNat width (old ++ [x1]).length))
        { s4 with
          memory := m'
          stack := init ++ old ++ [x1] ++ xs
          store := s4.store.updateListEq [(.temp 0, g0), (.temp 1, g1), (.temp 2, .word pb'),
            (.temp 3, .word ib')]
          regs := s4.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa'),
            (4, .word i'), (5, x1), (6, q6)] }
    obtain ⟨ck', r0, r1, r2, r5, r6, r7, u0, u1, hr⟩ := ih _ hlt' (w >>> (1 : Nat)) rfl xs
      (old ++ [x1]) new' st' i' pa' ib' pb' curr i'' pa'' ib'' pb'' m'' s5 hrec
      (by simp [s5, s4, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL,
        FUPDATE_HOL, hcurr])
      huse hus
      (by simp [s5, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [s5, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [s5, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [s5, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [s5, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [s5, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [s5, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [s5, s4, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq,
        FUPDATE_LIST_HOL])
      (by simp [s5, setVar, FUPDATE_HOL])
      (by simp [s5, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s5, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s5, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s5, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s5, setVar]) hsp
      (by simpa [s5, s4, setVar, hst] using hbound)
    refine ⟨ck + ck' + 1, r0, r1, r2, r5, r6, r7, u0, u1, ?_⟩
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
    rw [wordGenGcMoveBitmapCode_eq, evaluate_loop, evaluate_ite]
    simp only [getVar, HolRegImm.toWordRegImm, h7, StackSemStateOps.getVarImm, wordSemWordCmp,
      wordCmpHOL, hnlt']
    rw [bitmapBody_move _ { s with clock := s.clock + (ck + ck' + 1) } w old.length hw2
      hus h7 h8 hg hlen_le hj x hv hb, hs4,
      evaluate_seq_none _ _ _ _ hadd (by simp [s4, setVar]),
      evaluate_seq_none _ _ _ _ (stackStoreAny_eval _ 5 8 old.length x1 ?_ ?_ ?_ hg hlen_le ?_)
        le_rfl,
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
      ← wordGenGcMoveBitmapCode_eq]
    refine (congrArg (fun st => evaluate (wordGenGcMoveBitmapCode conf, st)) ?_).trans
      (hr.trans ?_)
    · simp only [s5, s4, setVar, hB x1, hsp, hst]
      congr 1
      simp
    · simp only [s5, s4, setVar, Prod.mk.injEq, true_and]
      rw [temps_updateListEq_twice]
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

namespace GenGcMoveBitmapSupport

/-- Canonical finite-support codec of the owning StackSem state carrier, required
by the `fmap_as_finite_support` qualifier of `word_gen_gc_move_bitmap_code_thm`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

end GenGcMoveBitmapSupport

/-- Exact HOL `word_gen_gc_move_bitmap_code_thm` (`stack_allocProofScript.sml:2805-2976`),
with HOL's binder order; HOL's free `conf` and `init` are implicit, and its
quantified `a1`, which the statement never mentions, is kept. `FLOOKUP s.store`,
`k IN FDOM`, `|++` and `get_var` are the canonical carrier's lookups,
`updateListEq` and `getVar`, `Temp nw` is `WordStore.temp n`, and
`dimindex (:'a) DIV 8` and `dimword (:'a)` are `width / 8` and `2 ^ width`; the
existentials `ck r0 r1 r2 r5 r6 r7 t0 t1` are kept. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem word_gen_gc_move_bitmap_code_thm {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {init : List (WordLocW width)} :
    ∀ (w : BitVec width) (stack : List (WordLocW width)) (s : StackSemStateFiniteExact width C F)
      (i pa ib pb curr : BitVec width) (m : BitVec width → WordLocW width)
      (dm : BitVec width → Bool) (new stack1 : List (WordLocW width))
      (_a1 i1 pa1 ib1 pb1 : BitVec width) (m1 : BitVec width → WordLocW width)
      (old : List (WordLocW width)),
      wordGenGcMoveBitmap conf (w, stack, i, pa, ib, pb, curr, m, dm) =
          some (new, stack1, i1, pa1, ib1, pb1, m1, true) ∧
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
        (s.store.lookup (.temp 0)).isSome = true ∧ (s.store.lookup (.temp 1)).isSome = true ∧
        s.store.lookup (.temp 2) = some (.word pb) ∧ s.store.lookup (.temp 3) = some (.word ib) ∧
        s.stack = init ++ old ++ stack ∧ s.stackSpace = init.length ∧
        (width / 8) * s.stack.length < 2 ^ width →
      ∃ ck r0 r1 r2 r5 r6 r7 t0 t1,
        evaluate (wordGenGcMoveBitmapCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m1
            stack := init ++ old ++ new ++ stack1
            store := s.store.updateListEq [(.temp 0, t0), (.temp 1, t1), (.temp 2, .word pb1),
              (.temp 3, .word ib1)]
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
              (4, .word i1), (5, r5), (6, r6), (7, r7),
              (8, .word (wordSemBytesInWord * BitVec.ofNat width (old ++ new).length))] }) := by
  rintro w stack s i pa ib pb curr m dm new stack1 _ i1 pa1 ib1 pb1 m1 old
    ⟨hm, hsl, hws, hw2, hlen, hg, hshift, hcurr, huse, rfl, rfl, hus, h0, h1, h2, h3, h4, h5, h6,
      h7, h8, ht0, ht1, ht2, ht3, hst, hsp, hbound⟩
  exact wordGenGcMoveBitmapCode_run hsl hws hw2 hlen hg hshift init w.toNat w rfl stack old new
    stack1 i pa ib pb curr i1 pa1 ib1 pb1 m1 s hm hcurr huse hus h0 h1 h2
    (by simpa [getVar] using h3) (by simpa [getVar] using h4) h5 h6 (by simpa [getVar] using h7)
    (by simpa [getVar] using h8) ht0 ht1 ht2 ht3 hst hsp hbound

end Flapjack.Compiler.Backend.StackAlloc
