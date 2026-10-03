import Flapjack.Compiler.Backend.LabSem.Inst
import Flapjack.Compiler.Backend.LabToTarget.ShareMemState
import Flapjack.Compiler.Backend.LabToTarget.WordLocation
import Flapjack.Compiler.Encoders.AsmSem.Step
import Mathlib.Tactic.SplitIfs

/-! Original register-relation preservation for the integer and FP updates of
`Inst_lemma` (lab_to_targetProofScript.sml:2005-2144). Source and target
updates are the reviewed native labSem and asmSem transitions; FP updates
inherit the reviewed rational-cut real translation (docs/SOUNDNESS.md item 8).
-/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Encoders Flapjack.Compiler.Encoders.Asm

/-- A source word register determines the related target register;
Flapjack infrastructure (HOL unfolds `word_loc_val_def`). -/
theorem wordLocVal_word_target {width : Nat} [NeZero width] {p : BitVec width}
    {labs : Spt (Spt Nat)} {v : WordLocW width} {w x : BitVec width}
    (h : wordLocVal p labs v = some x) (hv : v = .word w) : x = w := by
  subst hv
  simpa [wordLocVal] using h.symm

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "arith_upd_lemma"
  (words_as_type_indexed_bitvec)]
theorem arithUpd_lemma {width : Nat} [NeZero width] {C F : Type} (p : BitVec width)
    (labs : Spt (Spt Nat)) (a : HolArith width) (s1 : LabSem.State width C F)
    (t1 : AsmState width) :
    (∀ r, wordLocVal p labs (s1.regs r) = some (t1.regs r)) ∧
      ¬ (LabSem.arithUpd a s1).failed →
    ∀ r, wordLocVal p labs ((LabSem.arithUpd a s1).regs r) =
      some ((AsmSem.arithUpd a t1).regs r) := by
  rintro ⟨h, hf⟩ r
  have hw : ∀ r w, s1.regs r = .word w → t1.regs r = w :=
    fun r w e => wordLocVal_word_target (h r) e
  cases a with
  | binop op r1 r2 ri =>
    -- Both operands are words: the same binary operation on both sides.
    have hword : ∀ w1 w2, s1.regs r2 = .word w1 → LabSem.regImm ri s1 = .word w2 →
        wordLocVal p labs ((LabSem.arithUpd (.binop op r1 r2 ri) s1).regs r) =
          some ((AsmSem.arithUpd (.binop op r1 r2 ri) t1).regs r) := by
      intro w1 w2 e1 e2
      have h2 : AsmSem.regImm ri t1 = w2 := by
        cases ri with
        | reg r' => exact hw r' w2 (by simpa [LabSem.regImm] using e2)
        | imm v => simpa [LabSem.regImm, AsmSem.regImm] using e2
      simp only [LabSem.arithUpd, e1, e2, LabSem.binopUpd, LabSem.updReg, AsmSem.arithUpd,
        AsmSem.binopUpd, AsmSem.updReg, AsmSem.readReg, hw r2 w1 e1, h2]
      split
      · cases op <;> simp [wordLocVal]
      · exact h r
    cases hr2 : s1.regs r2 with
    | word w1 =>
      cases hri : LabSem.regImm ri s1 with
      | word w2 => exact hword w1 w2 hr2 hri
      | loc k1 k2 =>
        exfalso
        apply hf
        cases ri with
        | imm v => simp [LabSem.regImm] at hri
        | reg r' =>
          have hne : r' ≠ r2 := by
            rintro rfl
            simp [LabSem.regImm, hr2] at hri
          simp [LabSem.arithUpd, hr2, hri, hne, LabSem.assertState]
    | loc k1 k2 =>
      by_cases hc : op = .or ∧ ri = .reg r2
      · obtain ⟨rfl, rfl⟩ := hc
        simp only [LabSem.arithUpd, hr2, LabSem.regImm, beq_self_eq_true, and_self,
          ↓reduceIte, LabSem.updReg, AsmSem.arithUpd, AsmSem.binopUpd, AsmSem.updReg,
          AsmSem.regImm, AsmSem.readReg, BitVec.or_self]
        split
        · rw [← hr2]; exact h r2
        · exact h r
      · exfalso
        apply hf
        cases ri with
        | imm v => simp [LabSem.arithUpd, hr2, LabSem.regImm, LabSem.assertState]
        | reg r' =>
          have hn : ¬ (op = .or ∧ r' = r2) := fun ⟨h1, h2⟩ => hc ⟨h1, by rw [h2]⟩
          simp [LabSem.arithUpd, hr2, LabSem.regImm, LabSem.assertState, hn]
  | shift op r1 r2 ri =>
    cases hr2 : s1.regs r2 with
    | loc _ _ => exfalso; apply hf; simp [LabSem.arithUpd, hr2, LabSem.assertState]
    | word w1 =>
      cases hri : LabSem.regImm ri s1 with
      | loc _ _ => exfalso; apply hf; simp [LabSem.arithUpd, hr2, hri, LabSem.assertState]
      | word w2 =>
        have h2 : AsmSem.regImm ri t1 = w2 := by
          cases ri with
          | reg r' => exact hw r' w2 (by simpa [LabSem.regImm] using hri)
          | imm v => simpa [LabSem.regImm, AsmSem.regImm] using hri
        simp only [LabSem.arithUpd, hr2, hri, LabSem.assertState, LabSem.updReg,
          AsmSem.arithUpd, AsmSem.assertState, AsmSem.updReg, AsmSem.readReg, hw r2 w1 hr2, h2]
        split_ifs <;> first | exact h r | simp [wordLocVal]
  | div r1 r2 r3 =>
    cases hr3 : s1.regs r3 with
    | loc _ _ => exfalso; apply hf; simp [LabSem.arithUpd, hr3, LabSem.assertState]
    | word w3 =>
      cases hr2 : s1.regs r2 with
      | loc _ _ => exfalso; apply hf; simp [LabSem.arithUpd, hr3, hr2, LabSem.assertState]
      | word w2 =>
        have hdiv : w2 / w3 = BitVec.ofNat width (w2.toNat / w3.toNat) := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_udiv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
          exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) w2.isLt
        simp only [LabSem.arithUpd, hr3, hr2, LabSem.assertState, LabSem.updReg,
          AsmSem.arithUpd, AsmSem.assertState, AsmSem.updReg, AsmSem.readReg,
          hw r3 w3 hr3, hw r2 w2 hr2, hdiv]
        split_ifs <;> first | exact h r | simp [wordLocVal]
  | longMul r1 r2 r3 r4 =>
    cases hr3 : s1.regs r3 with
    | loc _ _ => exfalso; apply hf; simp [LabSem.arithUpd, hr3, LabSem.assertState]
    | word w3 =>
      cases hr4 : s1.regs r4 with
      | loc _ _ => exfalso; apply hf; simp [LabSem.arithUpd, hr3, hr4, LabSem.assertState]
      | word w4 =>
        simp only [LabSem.arithUpd, hr3, hr4, LabSem.updReg, AsmSem.arithUpd, AsmSem.updReg,
          AsmSem.readReg, hw r3 w3 hr3, hw r4 w4 hr4]
        split_ifs <;> first | exact h r | simp [wordLocVal]
  | longDiv r1 r2 r3 r4 r5 =>
    cases hr3 : s1.regs r3 with
    | loc _ _ => exfalso; apply hf; simp [LabSem.arithUpd, hr3, LabSem.assertState]
    | word w3 =>
      cases hr4 : s1.regs r4 with
      | loc _ _ => exfalso; apply hf; simp [LabSem.arithUpd, hr3, hr4, LabSem.assertState]
      | word w4 =>
        cases hr5 : s1.regs r5 with
        | loc _ _ =>
          exfalso; apply hf; simp [LabSem.arithUpd, hr3, hr4, hr5, LabSem.assertState]
        | word w5 =>
          simp only [LabSem.arithUpd, hr3, hr4, hr5, LabSem.assertState, LabSem.updReg,
            AsmSem.arithUpd, AsmSem.assertState, AsmSem.updReg, AsmSem.readReg,
            hw r3 w3 hr3, hw r4 w4 hr4, hw r5 w5 hr5]
          split_ifs <;> first | exact h r | simp [wordLocVal]
  | addCarry r1 r2 r3 r4 =>
    cases hr2 : s1.regs r2 with
    | loc _ _ => exfalso; apply hf; simp [LabSem.arithUpd, hr2, LabSem.assertState]
    | word w2 =>
      cases hr3 : s1.regs r3 with
      | loc _ _ => exfalso; apply hf; simp [LabSem.arithUpd, hr2, hr3, LabSem.assertState]
      | word w3 =>
        cases hr4 : s1.regs r4 with
        | loc _ _ =>
          exfalso; apply hf; simp [LabSem.arithUpd, hr2, hr3, hr4, LabSem.assertState]
        | word w4 =>
          simp only [LabSem.arithUpd, hr2, hr3, hr4, LabSem.updReg, AsmSem.arithUpd,
            AsmSem.updReg, AsmSem.readReg, hw r2 w2 hr2, hw r3 w3 hr3, hw r4 w4 hr4]
          split_ifs <;> first | exact h r | simp [wordLocVal]
  | addOverflow r1 r2 r3 r4 =>
    cases hr2 : s1.regs r2 with
    | loc _ _ => exfalso; apply hf; simp [LabSem.arithUpd, hr2, LabSem.assertState]
    | word w2 =>
      cases hr3 : s1.regs r3 with
      | loc _ _ => exfalso; apply hf; simp [LabSem.arithUpd, hr2, hr3, LabSem.assertState]
      | word w3 =>
        simp only [LabSem.arithUpd, hr2, hr3, LabSem.updReg, AsmSem.arithUpd,
          AsmSem.updReg, AsmSem.readReg, hw r2 w2 hr2, hw r3 w3 hr3]
        split_ifs <;> first | exact h r | simp [wordLocVal]
  | subOverflow r1 r2 r3 r4 =>
    cases hr2 : s1.regs r2 with
    | loc _ _ => exfalso; apply hf; simp [LabSem.arithUpd, hr2, LabSem.assertState]
    | word w2 =>
      cases hr3 : s1.regs r3 with
      | loc _ _ => exfalso; apply hf; simp [LabSem.arithUpd, hr2, hr3, LabSem.assertState]
      | word w3 =>
        simp only [LabSem.arithUpd, hr2, hr3, LabSem.updReg, AsmSem.arithUpd,
          AsmSem.updReg, AsmSem.readReg, hw r2 w2 hr2, hw r3 w3 hr3]
        split_ifs <;> first | exact h r | simp [wordLocVal]

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "fp_upd_lemma"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
theorem fpUpd_lemma {width : Nat} [NeZero width] {C F : Type} (p : BitVec width)
    (labs : Spt (Spt Nat)) (f : HolFp) (s1 : LabSem.State width C F)
    (t1 : AsmState width) :
    (∀ r, wordLocVal p labs (s1.regs r) = some (t1.regs r)) ∧
      (∀ r, s1.fpRegs r = t1.fpRegs r) ∧ ¬ (LabSem.fpUpd f s1).failed →
    (∀ r, (LabSem.fpUpd f s1).fpRegs r = (AsmSem.fpUpd f t1).fpRegs r) ∧
    ∀ r, wordLocVal p labs ((LabSem.fpUpd f s1).regs r) =
      some ((AsmSem.fpUpd f t1).regs r) := by
  rintro ⟨h, hfp, hf⟩
  have hw : ∀ r w, s1.regs r = .word w → t1.regs r = w :=
    fun r w e => wordLocVal_word_target (h r) e
  have hfp' : s1.fpRegs = t1.fpRegs := funext hfp
  cases f <;> simp only [LabSem.fpUpd, AsmSem.fpUpd, LabSem.readFpReg, AsmSem.readFpReg,
    hfp', LabSem.updReg, AsmSem.updReg, LabSem.updFpReg, AsmSem.updFpReg,
    LabSem.assertState, AsmSem.assertState, fpSemFpfma] at hf ⊢
  case fpMovToReg r1 r2 d =>
    by_cases h64 : width = 64
    · simp only [h64, ↓reduceIte]
      refine ⟨fun _ => trivial, fun r => ?_⟩
      split_ifs <;> first | exact h r | simp [wordLocVal]
    · simp only [h64, ↓reduceIte]
      refine ⟨fun _ => trivial, fun r => ?_⟩
      split_ifs <;> first | exact h r | simp [wordLocVal]
  case fpMovFromReg d r1 r2 =>
    by_cases h64 : width = 64
    · simp only [h64, ↓reduceIte] at hf ⊢
      cases e1 : s1.regs r1 with
      | loc _ _ => simp [e1] at hf
      | word w1 =>
        refine ⟨fun r => ?_, h⟩
        simp only [AsmSem.readReg, hw r1 w1 e1]
    · simp only [h64, ↓reduceIte] at hf ⊢
      cases e1 : s1.regs r1 with
      | loc _ _ => simp [e1] at hf
      | word w1 =>
        cases e2 : s1.regs r2 with
        | loc _ _ => simp [e1, e2] at hf
        | word w2 =>
          refine ⟨fun r => ?_, h⟩
          simp only [AsmSem.readReg, hw r1 w1 e1, hw r2 w2 e2]
  case fpToInt d1 d2 =>
    cases hi : holFp64ToInt .roundTiesToEven (t1.fpRegs d2) with
    | none => exact ⟨fun _ => rfl, h⟩
    | some n =>
      by_cases h64 : width = 64 <;> simp only [h64, ↓reduceIte] <;> exact ⟨fun _ => trivial, h⟩
  all_goals first
    | exact ⟨fun _ => trivial, h⟩
    | (refine ⟨fun _ => trivial, fun r => ?_⟩
       split_ifs <;> first | exact h r | simp_all [wordLocVal])

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "arith_upd_fp_regs"
  (words_as_type_indexed_bitvec)]
theorem arithUpd_fpRegs {width : Nat} [NeZero width] {C F : Type} (a : HolArith width)
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) (t : AsmState width) :
    (LabSem.arithUpd a s).fpRegs = s.fpRegs ∧ (AsmSem.arithUpd a t).fpRegs = t.fpRegs := by
  constructor
  · cases a <;> simp only [LabSem.arithUpd] <;> (repeat' split) <;>
      simp [LabSem.binopUpd, LabSem.updReg, LabSem.assertState]
  · cases a <;> simp [AsmSem.arithUpd, AsmSem.binopUpd, AsmSem.updReg, AsmSem.assertState]

/-- `share_mem_state_rel` reads the source state only through its FFI
state; Flapjack infrastructure for the original `share_mem_state_rel_def`
rewriting. -/
theorem shareMemStateRel_of_ffi {labWidth : Nat} [NeZero labWidth] {width : Nat} [NeZero width]
    {γ δ F ε ζ ε' ζ' : Type} (mc : MachineConfig width γ δ)
    (s s' : LabSem.State labWidth Config F) (t : ε) (ms : ζ) (t' : ε') (ms' : ζ')
    (hffi : s'.ffi = s.ffi) (h : shareMemStateRel mc s t ms) :
    shareMemStateRel mc s' t' ms' := by
  unfold shareMemStateRel at h ⊢
  rw [hffi]
  exact h

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "Inst_share_mem_pc_update_helper" (words_as_type_indexed_bitvec)]
theorem inst_shareMem_pcUpdate_helper {width : Nat} [NeZero width] {labWidth : Nat}
    [NeZero labWidth] {S Q F Z : Type}
    (mc : MachineConfig width S Q) (s1 : LabSem.State labWidth Config F) (t1 : AsmState width)
    (ms1 : Z) (ms2 : S) (pc' : BitVec width) :
    shareMemStateRel mc s1 t1 ms1 ∧ targetStateRel mc.target { t1 with pc := pc' } ms2 →
    shareMemStateRel mc { s1 with pc := s1.pc + 1, clock := s1.clock - 1 }
      { t1 with pc := pc' } ms2 :=
  fun h => shareMemStateRel_of_ffi mc s1 _ t1 ms1 _ ms2 rfl h.1

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "Inst_share_mem_reg_update_helper" (words_as_type_indexed_bitvec)]
theorem inst_shareMem_regUpdate_helper {width : Nat} [NeZero width] {S Q F Z : Type}
    (mc : MachineConfig width S Q) (s1 : LabSem.State width Config F) (t1 : AsmState width)
    (ms1 : Z) (ms2 : S) (pc' : BitVec width) (n : Nat) (c : BitVec width) :
    shareMemStateRel mc s1 t1 ms1 ∧
      targetStateRel mc.target
        { t1 with regs := (fun r => if r = n then c else t1.regs r), pc := pc' } ms2 →
    shareMemStateRel mc
      { s1 with
          regs := (fun r => if r = n then .word c else s1.regs r)
          pc := s1.pc + 1
          clock := s1.clock - 1 }
      { t1 with regs := (fun r => if r = n then c else t1.regs r), pc := pc' } ms2 :=
  fun h => shareMemStateRel_of_ffi mc s1 _ t1 ms1 _ ms2 rfl h.1

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "arith_upd_share_mem_domain_unchange" (words_as_type_indexed_bitvec)]
theorem arithUpd_sharedMemDomain {width : Nat} [NeZero width] {C F : Type}
    (a : HolArith width) (s1 : Flapjack.Compiler.Backend.LabSem.State width C F) :
    (LabSem.arithUpd a s1).sharedMemDomain = s1.sharedMemDomain := by
  cases a <;> simp only [LabSem.arithUpd] <;> (repeat' split) <;>
    simp [LabSem.binopUpd, LabSem.updReg, LabSem.assertState]

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "fp_upd_share_mem_domain_unchange" (words_as_type_indexed_bitvec)]
theorem fpUpd_sharedMemDomain {width : Nat} [NeZero width] {C F : Type}
    (f : HolFp) (s1 : Flapjack.Compiler.Backend.LabSem.State width C F) :
    (LabSem.fpUpd f s1).sharedMemDomain = s1.sharedMemDomain := by
  cases f <;> simp only [LabSem.fpUpd] <;> (repeat' split) <;>
    simp [LabSem.updReg, LabSem.updFpReg, LabSem.assertState]

end Flapjack.Compiler.Backend.LabToTarget
