import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.Memcpy
import Flapjack.Compiler.Backend.StackAlloc.Proofs.WordLemmas

/-!
# `stack_allocProof` `word_gc_move_code_thm`

`word_gc_move_code_thm` of
`cakeml/compiler/backend/proofs/stack_allocProofScript.sml` (875-961): the
stackLang `word_gc_move_code` run by the exact StackSem `evaluate` simulates the
shallow `word_gcFunctions` `word_gc_move` on a `Loc`, an untagged word, a
forwarding pointer and an object to copy (through `memcpy_code_thm`).
`memcpyCode_eval` restates `memcpy_code_thm` as a rewrite with a chosen register-1
value; it and the remaining lemmas are Flapjack infrastructure.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackRemove (loadInst storeInst leftShiftInst rightShiftInst)

theorem wordGcMoveCode_eq {width : Nat} [NeZero width] (conf : Config) :
    (wordGcMoveCode conf : HolProg width) = .ite .test 5 (.imm 1) .skip
      (listSeqHOL [moveHOL 0 5, .get 1 .currHeap, rightShiftInst 0 (shiftLength conf),
        leftShiftInst 0 (wordShiftAmount width), addInst 0 1, loadInst 1 0,
        .ite .test 1 (.imm 3)
          (listSeqHOL [rightShiftInst 1 2, leftShiftInst 1 (shiftLength conf),
            clearTopInst 5 (smallShiftLength conf - 1), orInst 5 1])
          (listSeqHOL [rightShiftInst 1 (width - conf.lenSize), add1Inst 1, moveHOL 6 1,
            moveHOL 2 0, moveHOL 0 1, memcpyCode, moveHOL 0 6,
            leftShiftInst 0 (wordShiftAmount width), subInst 2 0, moveHOL 0 4,
            leftShiftInst 0 2, storeInst 0 2, moveHOL 1 4,
            clearTopInst 5 (smallShiftLength conf - 1), leftShiftInst 1 (shiftLength conf),
            orInst 5 1, addInst 4 6])]) := rfl

/-- The skip outcome: the code leaves the state unchanged and the seven
registers keep their values. -/
theorem gcMove_skip_regs {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (r0 r1 r2 r6 pa i w : WordLocW width)
    (h0 : s.regs.lookup 0 = some r0) (h1 : s.regs.lookup 1 = some r1)
    (h2 : s.regs.lookup 2 = some r2) (h3 : s.regs.lookup 3 = some pa)
    (h4 : s.regs.lookup 4 = some i) (h5 : s.regs.lookup 5 = some w)
    (h6 : s.regs.lookup 6 = some r6) :
    s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, pa), (4, i), (5, w), (6, r6)] =
      s.regs := by
  apply regs_ext
  intro k
  simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl, FUPDATE_HOL]
  by_cases k0 : k = 0
  · subst k0; simp [h0]
  by_cases k1 : k = 1
  · subst k1; simp [h1]
  by_cases k2 : k = 2
  · subst k2; simp [h2]
  by_cases k3 : k = 3
  · subst k3; simp [h3]
  by_cases k4 : k = 4
  · subst k4; simp [h4]
  by_cases k5 : k = 5
  · subst k5; simp [h5]
  by_cases k6 : k = 6
  · subst k6; simp [h6]
  simp [k0, k1, k2, k3, k4, k5, k6]

/-- The register-1 value left by `memcpy_code` (HOL's existential `r1`), chosen
by `Classical.epsilon`. Flapjack infrastructure for rewriting with
`memcpy_code_thm` inside a larger program. -/
noncomputable def memcpyR1 {width : Nat} [NeZero width] {C F : Type}
    (S : StackSemStateFiniteExact width C F) (w a b : BitVec width) : WordLocW width :=
  Classical.epsilon (fun r1 => evaluate (memcpyCode, S) =
    (none, { S with
      clock := S.clock - w.toNat
      memory := (WordGcFunctions.memcpy w a b S.memory S.mdomain).2.1
      regs := S.regs.updateListEq [(0, .word 0), (1, r1), (2, .word (a + w * wordSemBytesInWord)),
        (3, .word (WordGcFunctions.memcpy w a b S.memory S.mdomain).1)] }))

/-- `memcpy_code_thm` as a conditional rewrite on an arbitrary state. -/
theorem memcpyCode_eval {width : Nat} [NeZero width] {C F : Type}
    (S : StackSemStateFiniteExact width C F) (w a b : BitVec width)
    (h0 : S.regs.lookup 0 = some (.word w)) (h1 : (S.regs.lookup 1).isSome = true)
    (h2 : S.regs.lookup 2 = some (.word a)) (h3 : S.regs.lookup 3 = some (.word b))
    (hc : (WordGcFunctions.memcpy w a b S.memory S.mdomain).2.2 = true)
    (hck : w.toNat ≤ S.clock) :
    evaluate (memcpyCode, S) =
      (none, { S with
        clock := S.clock - w.toNat
        memory := (WordGcFunctions.memcpy w a b S.memory S.mdomain).2.1
        regs := S.regs.updateListEq [(0, .word 0), (1, memcpyR1 S w a b),
          (2, .word (a + w * wordSemBytesInWord)),
          (3, .word (WordGcFunctions.memcpy w a b S.memory S.mdomain).1)] }) := by
  let T : StackSemStateFiniteExact width C F := { S with clock := S.clock - w.toNat }
  have hT : ({ T with clock := T.clock + w.toNat } : StackSemStateFiniteExact width C F) = S := by
    simp only [T]; congr 1; omega
  have hm : WordGcFunctions.memcpy w a b T.memory T.mdomain =
      ((WordGcFunctions.memcpy w a b S.memory S.mdomain).1,
        (WordGcFunctions.memcpy w a b S.memory S.mdomain).2.1, true) := by
    simp only [T]; rw [← hc]
  obtain ⟨r1, hr⟩ := memcpy_code_thm w a b T.memory T.mdomain _ _ T
    ⟨hm, rfl, rfl, by simpa [getVar, T] using h0, by simpa [T] using h1,
      by simpa [getVar, T] using h2, by simpa [getVar, T] using h3⟩
  rw [hT] at hr
  have := Classical.epsilon_spec (p := fun r1 => evaluate (memcpyCode, S) =
    (none, { S with
      clock := S.clock - w.toNat
      memory := (WordGcFunctions.memcpy w a b S.memory S.mdomain).2.1
      regs := S.regs.updateListEq [(0, .word 0), (1, r1), (2, .word (a + w * wordSemBytesInWord)),
        (3, .word (WordGcFunctions.memcpy w a b S.memory S.mdomain).1)] })) ⟨r1, by
      rw [hr]⟩
  exact this

namespace GcMoveSupport

/-- Canonical finite-support codec of the owning StackSem state carrier, required
by the `fmap_as_finite_support` qualifier of `word_gc_move_code_thm`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

end GcMoveSupport

/-- Exact HOL `word_gc_move_code_thm` (`stack_allocProofScript.sml:875-961`). HOL's
free variables are implicit; `FLOOKUP s.store CurrHeap`, `k IN FDOM s.regs`,
`|++` and `get_var` are the canonical carrier's lookups, `updateListEq` and
`getVar`; the existentials `ck r0 r1 r2 r6` are kept. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "word_gc_move_code_thm"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_gc_move_code_thm {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    {w : WordLocW width} {i pa old : BitVec width} {m : BitVec width → WordLocW width}
    {dm : BitVec width → Bool} {w1 : WordLocW width} {i1 pa1 : BitVec width}
    {m1 : BitVec width → WordLocW width} {s : StackSemStateFiniteExact width C F} :
    wordGcMove conf (w, i, pa, old, m, dm) = (w1, i1, pa1, m1, true) ∧
      shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
      conf.lenSize ≠ 0 ∧
      (∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord) ∧
      s.store.lookup .currHeap = some (.word old) ∧ s.useStore = true ∧
      s.memory = m ∧ s.mdomain = dm ∧
      (s.regs.lookup 0).isSome = true ∧ (s.regs.lookup 1).isSome = true ∧
      (s.regs.lookup 2).isSome = true ∧
      getVar 3 s = some (.word pa) ∧ getVar 4 s = some (.word i) ∧ getVar 5 s = some w ∧
      (s.regs.lookup 6).isSome = true →
    ∃ ck r0 r1 r2 r6, evaluate (wordGcMoveCode conf, { s with clock := s.clock + ck }) =
      (none, { s with
        memory := m1
        regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1), (4, .word i1),
          (5, w1), (6, r6)] }) := by
  rintro ⟨hmove, hsl, hws, hw2, hlen, hshift, hcurr, huse, rfl, rfl, h0, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.1 h0
  obtain ⟨r1, hr1⟩ := Option.isSome_iff_exists.1 h1
  obtain ⟨r2, hr2⟩ := Option.isSome_iff_exists.1 h2
  obtain ⟨r6, hr6⟩ := Option.isSome_iff_exists.1 h6
  have h3' : s.regs.lookup 3 = some (.word pa) := by simpa [getVar] using h3
  have h4' : s.regs.lookup 4 = some (.word i) := by simpa [getVar] using h4
  have h5' : s.regs.lookup 5 = some w := by simpa [getVar] using h5
  cases w with
  | loc l1 l2 =>
      simp only [wordGcMove, Prod.mk.injEq, decide_eq_true_eq] at hmove
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hmove
      refine ⟨0, r0, r1, r2, r6, ?_⟩
      rw [gcMove_skip_regs s r0 r1 r2 r6 _ _ _ hr0 hr1 hr2 h3' h4' h5' hr6]
      rw [wordGcMoveCode_eq, evaluate_ite]
      simp [getVar, h5', StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, wordSemWordCmp,
        evaluate_skip]
  | word v =>
      by_cases hv : v &&& 1 = 0
      · simp only [wordGcMove, hv, if_true, Prod.mk.injEq] at hmove
        obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hmove
        refine ⟨0, r0, r1, r2, r6, ?_⟩
        rw [gcMove_skip_regs s r0 r1 r2 r6 _ _ _ hr0 hr1 hr2 h3' h4' h5' hr6]
        rw [wordGcMoveCode_eq, evaluate_ite]
        have hv' : AndOp.and v (1#width) = 0#width := hv
        simp [getVar, h5', StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, wordSemWordCmp,
          wordCmpHOL, hv', evaluate_skip]
      · have hv0 : ¬ AndOp.and v (1#width) = 0#width := hv
        have hv' : (AndOp.and v (1#width) == 0#width) = false := by simpa using hv0
        have hsl_le : ¬ width ≤ shiftLength conf := by omega
        have hws_le : ¬ width ≤ wordShiftAmount width := by omega
        have h2_le : ¬ width ≤ 2 := by omega
        have hpow : width < 2 ^ width := Nat.lt_two_pow_self
        have hkm : (width - (smallShiftLength conf - 1) - 1) % 2 ^ width =
            width - (smallShiftLength conf - 1) - 1 :=
          Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt
            (show width - (smallShiftLength conf - 1) - 1 ≤ width by omega) hpow)
        have hk_le : ¬ width ≤ width - (smallShiftLength conf - 1) - 1 := by omega
        have haddr : (v >>> shiftLength conf <<< wordShiftAmount width) + old =
            ptrToAddr conf old v := by
          rw [hshift, ptrToAddr, BitVec.add_comm]
        have hslm : shiftLength conf % 2 ^ width = shiftLength conf := Nat.mod_eq_of_lt (by omega)
        have hwsm : wordShiftAmount width % 2 ^ width = wordShiftAmount width :=
          Nat.mod_eq_of_lt (by omega)
        have h2m : 2 % 2 ^ width = 2 := Nat.mod_eq_of_lt (by omega)
        have hr1' := hr1
        have hcur : s.store.lookup (StackSemRegisterTransfers.storeOfSyntax .currHeap) =
            some (.word old) := hcurr
        simp only [wordGcMove, hv, if_false] at hmove
        by_cases hfwd : wordSemIsFwdPtr (s.memory (ptrToAddr conf old v)) = true
        · simp only [hfwd, if_true, Prod.mk.injEq] at hmove
          obtain ⟨rfl, rfl, rfl, rfl, hdm⟩ := hmove
          obtain ⟨x, hx, hx3⟩ := (is_fwd_ptr_iff _).1 hfwd
          have hx3a : AndOp.and x (3#width) = 0#width := hx3
          have hx3' : (AndOp.and x (3#width) == 0#width) = true := by simpa using hx3a
          refine ⟨0, .word (((v >>> shiftLength conf) <<< wordShiftAmount width) + old),
            .word ((x >>> 2) <<< shiftLength conf), r2, r6, ?_⟩
          rw [wordGcMoveCode_eq, evaluate_ite]
          simp [getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, wordSemWordCmp,
            wordCmpHOL, hv', listSeqHOL, evaluate_seq, evaluate_inst, evaluate_get, evaluate_ite,
            moveHOL, clearTopInst, orInst, loadInst, addInst, rightShiftInst, leftShiftInst,
            StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
            StackSemExpressions.assign, StackSemExpressions.wordExp, setVar, memLoad, wordOpHOL,
            wordOp, fixClock, huse, hcur, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, h5',
            hslm, hwsm, h2m, wordShiftHOL, hsl_le, hws_le, h2_le, haddr, hdm, hx, hx3', hkm, hk_le]
          have hor : ∀ a b : BitVec width, OrOp.or a b = a ||| b := fun _ _ => rfl
          apply regs_ext
          intro k
          simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl,
            FUPDATE_HOL, HolFiniteMapExact.lookup_updateEq]
          by_cases k0 : k = 0
          · subst k0; simp
          by_cases k1 : k = 1
          · subst k1; simp
          by_cases k2 : k = 2
          · subst k2; simp [hr2]
          by_cases k3 : k = 3
          · subst k3; simp [h3']
          by_cases k4 : k = 4
          · subst k4; simp [h4']
          by_cases k5 : k = 5
          · subst k5; simp [hor, updateAddr, select_lower_lemma, BitVec.or_comm]
          by_cases k6 : k = 6
          · subst k6; simp [hr6]
          simp [k0, k1, k2, k3, k4, k5, k6]
        · have hfwd' : wordSemIsFwdPtr (s.memory (ptrToAddr conf old v)) = false := by
            simpa using hfwd
          simp only [hfwd', Bool.false_eq_true, if_false] at hmove
          have hc := congrArg (fun t => t.2.2.2.2) hmove
          simp only [Bool.and_eq_true] at hc
          obtain ⟨⟨hdm, -, hisw⟩, -, hc1⟩ := hc
          obtain ⟨x, hx⟩ := (isWord_thm _).1 hisw
          have hx3 : ¬ x &&& 3 = 0 := by simpa [hx, wordSemIsFwdPtr] using hfwd'
          simp only [hx, wordSemTheWord, Prod.mk.injEq] at hmove hc1
          obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hmove
          have hx3a : ¬ AndOp.and x (3#width) = 0#width := hx3
          have hx3' : (AndOp.and x (3#width) == 0#width) = false := by simpa using hx3a
          have hlm : (width - conf.lenSize) % 2 ^ width = width - conf.lenSize :=
            Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (show width - conf.lenSize ≤ width by omega) hpow)
          have hl_le : ¬ width ≤ width - conf.lenSize := by omega
          have hdec : x >>> (width - conf.lenSize) = decodeLength conf x := rfl
          refine ⟨(decodeLength conf x + 1).toNat, .word (i <<< 2), .word (i <<< shiftLength conf),
            .word (ptrToAddr conf old v), .word (decodeLength conf x + 1), ?_⟩
          rw [wordGcMoveCode_eq, evaluate_ite]
          simp [getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, wordSemWordCmp,
            wordCmpHOL, hv', listSeqHOL, evaluate_seq, evaluate_inst, evaluate_get, evaluate_ite,
            moveHOL, clearTopInst, orInst, loadInst, storeInst, addInst, subInst, add1Inst,
            rightShiftInst, leftShiftInst, StackSemInst.instHOL,
            StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
            StackSemExpressions.wordExp, setVar, memLoad, memStore, wordOpHOL, wordOp, fixClock,
            huse, hcur, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, h5', hslm, hwsm, h2m,
            wordShiftHOL, hsl_le, hws_le, haddr, hdm, hx, hx3', hlm, hl_le, hdec]
          rw [memcpyCode_eval _ (decodeLength conf x + 1) (ptrToAddr conf old v) pa ?_ ?_ ?_ ?_ ?_ ?_]
          rotate_left
          · simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
          · simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
          · simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
          · simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, h3']
          · exact hc1
          · simp
          have hback : ptrToAddr conf old v + (decodeLength conf x + 1#width) * wordSemBytesInWord -
              (decodeLength conf x <<< wordShiftAmount width + 1#width <<< wordShiftAmount width) =
              ptrToAddr conf old v := by
            rw [hshift, hshift, ← BitVec.add_mul, BitVec.add_sub_cancel]
          simp [HolFiniteMapExact.lookup_updateEq, HolFiniteMapExact.lookup_updateListEq,
            FUPDATE_LIST_HOL, List.foldl, FUPDATE_HOL, hslm, hwsm, h2m, hsl_le, hws_le, h2_le, hdm,
            hkm, hk_le, h4', h5', hback]
          have hor : ∀ a b : BitVec width, OrOp.or a b = a ||| b := fun _ _ => rfl
          refine ⟨?_, ?_⟩
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
            · subst k4; simp [BitVec.add_assoc]
            by_cases k5 : k = 5
            · subst k5; simp [hor, updateAddr, select_lower_lemma, BitVec.or_comm]
            by_cases k6 : k = 6
            · subst k6; simp
            simp [k0, k1, k2, k3, k4, k5, k6]
          · funext key
            simp [gcUpdate, eq_comm]

end Flapjack.Compiler.Backend.StackAlloc
