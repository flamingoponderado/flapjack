import Flapjack.Compiler.Backend.LabToTarget.InstMem

/-! Original instruction simulation `Inst_lemma`
(lab_to_targetProofScript.sml:2170-2932) over the native labSem and asmSem
transitions and the full native `state_rel`. -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Encoders Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem

/-- Target arithmetic succeeds whenever the related source arithmetic does;
Flapjack infrastructure for the `conj_asm1_tac` step of the original proof. -/
theorem arithUpd_target_notFailed {width : Nat} [NeZero width] {C F : Type}
    (p : BitVec width) (labs : Spt (Spt Nat)) (a : HolArith width)
    (s1 : LabSem.State width C F) (t1 : AsmState width)
    (h : ∀ r, wordLocVal p labs (s1.regs r) = some (t1.regs r)) (ht : t1.failed = false)
    (hf : ¬ (LabSem.arithUpd a s1).failed) : ¬ (AsmSem.arithUpd a t1).failed := by
  have hw : ∀ r w, s1.regs r = .word w → t1.regs r = w :=
    fun r w e => wordLocVal_word_target (h r) e
  cases a with
  | binop op r1 r2 ri =>
    cases op <;> simp [AsmSem.arithUpd, AsmSem.binopUpd, AsmSem.updReg, ht]
  | shift op r1 r2 ri =>
    cases hr2 : s1.regs r2 with
    | loc _ _ => exfalso; apply hf; simp [LabSem.arithUpd, hr2, LabSem.assertState]
    | word w1 =>
      cases hri : LabSem.regImm ri s1 with
      | loc _ _ => exfalso; apply hf; simp [LabSem.arithUpd, hr2, hri, LabSem.assertState]
      | word w2 =>
        simp only [LabSem.arithUpd, hr2, hri, LabSem.assertState, LabSem.updReg,
          Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_or, not_not] at hf
        cases ri with
        | imm v => simp [AsmSem.arithUpd, AsmSem.assertState, AsmSem.updReg, ht]
        | reg r' =>
          have e := hw r' w2 (by simpa [LabSem.regImm] using hri)
          simp [AsmSem.arithUpd, AsmSem.assertState, AsmSem.updReg, AsmSem.readReg, e, ht,
            hf.1]
  | div r1 r2 r3 =>
    cases hr3 : s1.regs r3 with
    | loc _ _ => exfalso; apply hf; simp [LabSem.arithUpd, hr3, LabSem.assertState]
    | word w3 =>
      cases hr2 : s1.regs r2 with
      | loc _ _ => exfalso; apply hf; simp [LabSem.arithUpd, hr3, hr2, LabSem.assertState]
      | word w2 =>
        simp only [LabSem.arithUpd, hr3, hr2, LabSem.assertState, LabSem.updReg,
          Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_or, not_not] at hf
        simpa [AsmSem.arithUpd, AsmSem.assertState, AsmSem.updReg, AsmSem.readReg,
          hw r3 w3 hr3, ht] using hf.1
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
            Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_or, not_not] at hf
          simp [AsmSem.arithUpd, AsmSem.assertState, AsmSem.updReg, AsmSem.readReg,
            hw r3 w3 hr3, hw r4 w4 hr4, hw r5 w5 hr5, ht, hf.1]
  | longMul => simp [AsmSem.arithUpd, AsmSem.updReg, ht]
  | addCarry => simp [AsmSem.arithUpd, AsmSem.updReg, ht]
  | addOverflow => simp [AsmSem.arithUpd, AsmSem.updReg, ht]
  | subOverflow => simp [AsmSem.arithUpd, AsmSem.updReg, ht]

/-- Target FP updates succeed whenever the related source update does;
Flapjack infrastructure. -/
theorem fpUpd_target_notFailed {width : Nat} [NeZero width] {C F : Type}
    (f : HolFp) (s1 : LabSem.State width C F) (t1 : AsmState width)
    (hfp : ∀ r, s1.fpRegs r = t1.fpRegs r) (ht : t1.failed = false)
    (hf : ¬ (LabSem.fpUpd f s1).failed) : ¬ (AsmSem.fpUpd f t1).failed := by
  have hfp' : s1.fpRegs = t1.fpRegs := funext hfp
  cases f <;> simp only [LabSem.fpUpd, AsmSem.fpUpd, LabSem.readFpReg, AsmSem.readFpReg,
    hfp', LabSem.updReg, AsmSem.updReg, LabSem.updFpReg, AsmSem.updFpReg,
    LabSem.assertState, AsmSem.assertState, ht] at hf ⊢
  case fpMovToReg => split <;> simp
  case fpToInt d1 d2 =>
    cases hi : holFp64ToInt .roundTiesToEven (t1.fpRegs d2) with
    | none => simp [hi] at hf
    | some n => by_cases h64 : width = 64 <;> simp_all
  all_goals simp

/-- Source arithmetic and FP updates leave memory unchanged; Flapjack
infrastructure. -/
theorem arithUpd_memory {width : Nat} [NeZero width] {C F : Type} (a : HolArith width)
    (s : LabSem.State width C F) : (LabSem.arithUpd a s).memory = s.memory := by
  cases a <;> simp only [LabSem.arithUpd] <;> (repeat' split) <;>
    simp [LabSem.binopUpd, LabSem.updReg, LabSem.assertState]

theorem fpUpd_memory {width : Nat} [NeZero width] {C F : Type} (f : HolFp)
    (s : LabSem.State width C F) : (LabSem.fpUpd f s).memory = s.memory := by
  cases f <;> simp only [LabSem.fpUpd] <;> (repeat' split) <;>
    simp [LabSem.updReg, LabSem.updFpReg, LabSem.assertState]

/-- The register-only instructions: Skip, Const, Arith and FP. -/
theorem instSim_nonMem {width : Nat} [NeZero width] {C F : Type} (p : BitVec width)
    (labs : Spt (Spt Nat)) (i : HolInst width) (s1 : LabSem.State width C F)
    (t1 : AsmState width) (hi : ∀ m r a, i ≠ .mem m r a)
    (hregs : ∀ r, wordLocVal p labs (s1.regs r) = some (t1.regs r))
    (hfp : ∀ r, s1.fpRegs r = t1.fpRegs r)
    (hmem : ∀ a, s1.memDomain (holByteAlign a) = true →
      wordLocValByte p labs s1.memory a s1.be = some (t1.mem a))
    (ht : t1.failed = false) (hf : ¬ (asmInst i s1).failed) :
    InstSim p labs i s1 t1 := by
  cases i with
  | skip => exact ⟨by simpa [AsmSem.instUpd] using ht, fun _ _ => rfl, hregs, hfp, hmem⟩
  | const r w =>
    refine ⟨by simpa [AsmSem.instUpd, AsmSem.updReg] using ht, fun _ _ => rfl, ?_, hfp, hmem⟩
    intro r'
    simp only [asmInst, LabSem.updReg, AsmSem.instUpd, AsmSem.updReg]
    split_ifs
    · simp [wordLocVal]
    · exact hregs r'
  | arith a =>
    have hf' : ¬ (LabSem.arithUpd a s1).failed := hf
    have htm := (AsmProps.arithUpd_consts a t1).2.2.1
    refine ⟨arithUpd_target_notFailed p labs a s1 t1 hregs ht hf',
      fun x _ => by simp [AsmSem.instUpd, htm], arithUpd_lemma p labs a s1 t1 ⟨hregs, hf'⟩,
      ?_, ?_⟩
    · intro r
      simp only [asmInst, AsmSem.instUpd, (arithUpd_fpRegs a s1 t1).1,
        (arithUpd_fpRegs a s1 t1).2]
      exact hfp r
    · intro x hx
      simp only [asmInst, AsmSem.instUpd, arithUpd_memory, htm]
      exact hmem x hx
  | fp f =>
    have hf' : ¬ (LabSem.fpUpd f s1).failed := hf
    have htm := (AsmProps.fpUpd_consts f t1).2.2.1
    have hl := fpUpd_lemma p labs f s1 t1 ⟨hregs, hfp, hf'⟩
    refine ⟨fpUpd_target_notFailed f s1 t1 hfp ht hf',
      fun x _ => by simp [AsmSem.instUpd, htm], hl.2, hl.1, ?_⟩
    intro x hx
    simp only [asmInst, AsmSem.instUpd, fpUpd_memory, htm]
    exact hmem x hx
  | mem m r a => exact absurd rfl (hi m r a)

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "Inst_lemma"
  (words_as_type_indexed_bitvec)]
theorem instLemma {width : Nat} [NeZero width] {S Q F : Type}
    (i : HolInst width) (s1 : LabSem.State width Config F)
    (mc : MachineConfig width S Q) (code2 : LabProgHOL width) (labs : Spt (Spt Nat))
    (p : BitVec width) (t1 : AsmState width) (ms1 : S) (bytes' : List (BitVec 8))
    (ms2 : S) :
    ¬ (asmInst i s1).failed ∧ stateRel (mc, code2, labs, p) s1 t1 ms1 ∧
      posVal (s1.pc + 1) 0 code2 = posVal s1.pc 0 code2 + bytes'.length →
    ¬ (AsmSem.instUpd i t1).failed ∧
    (∀ a, ¬ s1.memDomain a = true → (AsmSem.instUpd i t1).mem a = t1.mem a) ∧
    (targetStateRel mc.target
        (AsmSem.updPc (t1.pc + BitVec.ofNat width bytes'.length) (AsmSem.instUpd i t1)) ms2 →
      stateRel (mc, code2, labs, p) (incPc (decClock (asmInst i s1)))
        (AsmSem.updPc (t1.pc + BitVec.ofNat width bytes'.length) (AsmSem.instUpd i t1)) ms2) := by
  rintro ⟨hf, hrel, hpos⟩
  obtain ⟨-, c2, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    c29, c30, c31, -, -, -, -, -, -, hs1f, ht1f, c40, htpc, -⟩ := id hrel
  have hsim : InstSim p labs i s1 t1 := by
    cases i with
    | mem m r a => exact instSim_mem ⟨c2, c30, c29, c31, ht1f, c40⟩ m r a hf
    | _ =>
      exact instSim_nonMem p labs _ s1 t1 (by intros; simp) c30 c29
        (fun x hx => (c31 x hx).2.2) ht1f hf
  obtain ⟨htf, hout, hregs, hfp, hmem⟩ := hsim
  refine ⟨htf, hout, fun htrel => ?_⟩
  rw [incPc_decClock_asmInst_eq i s1 hs1f hf]
  rw [updPc_instUpd_eq i t1 _ ht1f htf] at htrel ⊢
  refine stateRel_frame hrel _ _ _ _ _ _ _ _ _ htrel hregs hfp hmem hout ?_
  rw [htpc, hpos, BitVec.add_assoc, ← BitVec.ofNat_add]

end Flapjack.Compiler.Backend.LabToTarget
