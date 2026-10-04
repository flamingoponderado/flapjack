import Flapjack.Compiler.Backend.LabToTarget.CompileCorrect.Install
import Flapjack.Compiler.Backend.LabToTarget.CompileCorrect.Control
import Flapjack.Compiler.Backend.LabToTarget.CompileCorrect.Cbw

/-! The original `compile_correct` (lab_to_targetProofScript.sml:7528-7558),
assembled from its cases by the source's `evaluate_ind` induction, which this
file realises as strong induction on the source clock: every recursive call
of `LabSem.evaluate` runs on a state whose clock is one less. -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Encoders Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.AsmSem Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabLang

/-- A source state whose evaluation is an `Error` satisfies the conclusion
vacuously (the original's `res <> Error` premise). -/
theorem compileCorrect_error {width : Nat} [NeZero width] {S Q F : Type}
    (s1 : LabSem.State width Config F) (h : evaluate s1 = (.error, s1)) :
    CompileCorrectFor S Q s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨-, hev, hres, -, -⟩
  rw [h] at hev
  exact absurd (Prod.mk.inj hev).1.symm hres

/-- A timed-out source state is matched by the target with no extra clock. -/
theorem compileCorrect_timeOut {width : Nat} [NeZero width] {S Q F : Type}
    (s1 : LabSem.State width Config F) (hc : s1.clock = 0) :
    CompileCorrectFor S Q s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨-, hev, -, -, -⟩
  rw [evaluate, if_pos hc] at hev
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
  exact ⟨0, ms1, by rw [hc]; rfl⟩

/-- Every source state satisfies the original `compile_correct` conclusion:
the cases of the original proof, combined by strong induction on the source
clock (the original's `evaluate_ind`). -/
theorem compileCorrectFor_all {width : Nat} [NeZero width] {S Q F : Type}
    (s1 : LabSem.State width Config F) : CompileCorrectFor S Q s1 := by
  induction hcl : s1.clock using Nat.strong_induction_on generalizing s1 with
  | _ c ihc =>
  have IH : ∀ s' : LabSem.State width Config F, s'.clock < s1.clock →
      CompileCorrectFor S Q s' := fun s' hs => ihc _ (hcl ▸ hs) s' rfl
  by_cases hc : s1.clock = 0
  · exact compileCorrect_timeOut s1 hc
  have herr : ∀ (h : evaluate s1 = (.error, s1)), CompileCorrectFor S Q s1 :=
    compileCorrect_error s1
  cases hf : asmFetch s1 with
  | none => exact herr (by rw [evaluate]; simp [hc, hf])
  | some line =>
  cases line with
  | label => exact herr (by rw [evaluate]; simp [hc, hf])
  | asm a bytes n =>
    cases a with
    | asmi i =>
      cases i with
      | inst ins =>
        exact compileCorrect_asmInst s1 ins bytes n hc hf fun _ => IH _ (by
          obtain ⟨-, -, hcl', -⟩ := asmInstConsts ins s1
          simp [incPc, decClock, hcl']; omega)
      | jumpReg r =>
        exact compileCorrect_jumpReg s1 r bytes n hc hf fun _ _ _ _ _ => IH _ (by
          simp [LabSem.updPc, decClock]; omega)
      | _ => exact herr (by rw [evaluate]; simp [hc, hf])
    | cbw r1 r2 =>
      exact compileCorrect_cbw s1 r1 r2 bytes n hc hf fun _ _ _ _ _ _ => IH _ (by
        simp [incPc, decClock]; omega)
    | shareMem m r ad =>
      exact compileCorrect_shareMem s1 m r ad bytes n hc hf fun ffi' bs s' hs => IH _ (by
        have := shareMemOp_ret_clock m r ad s1 s' ffi' bs hs
        simp only; omega)
  | labAsm a w bytes n =>
    cases a with
    | jump jt =>
      exact compileCorrect_jump s1 jt w bytes n hc hf fun _ _ => IH _ (by
        simp [LabSem.updPc, decClock]; omega)
    | jumpCmp cmp rr ri jt =>
      exact compileCorrect_jumpCmp s1 cmp rr ri jt w bytes n hc hf
        (fun _ => IH _ (by simp [incPc, decClock]; omega))
        (fun _ _ _ => IH _ (by simp [LabSem.updPc, decClock]; omega))
    | call lab =>
      exact compileCorrect_call s1 lab w bytes n hc hf fun _ _ _ _ => IH _ (by
        simp [LabSem.updPc, decClock, LabSem.updReg]; omega)
    | locValue reg lab =>
      exact compileCorrect_locValue s1 reg lab w bytes n hc hf fun _ => IH _ (by
        simp [incPc, decClock, LabSem.updReg]; omega)
    | install =>
      exact compileCorrect_install s1 w bytes n hc hf
        fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => IH _ (by simp only; omega)
    | callFFI name =>
      exact compileCorrect_callFFI s1 name w bytes n hc hf
        fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => IH _ (by simp only; omega)
    | halt => exact compileCorrect_halt s1 w bytes n hc hf

/-- The original `compile_correct`. HOL's existential binds an unused `t2` of
an otherwise unconstrained type variable; it is retained over an arbitrary
`T`, nonempty as every HOL type is. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileCorrect {width : Nat} [NeZero width] {S Q : Type} {F : Type} {T : Type}
    [Nonempty T] (p : BitVec width) (s1 : Flapjack.Compiler.Backend.LabSem.State width Config F)
    (res : MachineResult) (mc : MachineConfig width S Q)
    (s2 : Flapjack.Compiler.Backend.LabSem.State width Config F) (code2 : LabProgHOL width)
    (labs : Spt (Spt Nat)) (t1 : AsmState width) (ms1 : S) :
    oracleTie mc ms1 s1 ∧ evaluate s1 = (res, s2) ∧ res ≠ .error ∧
      encoderCorrect mc.target ∧ stateRel (mc, code2, labs, p) s1 t1 ms1 →
    ∃ (k : Nat) (_t2 : T) (ms2 : S),
      evaluateTargetHOL mc s1.ffi (s1.clock + k) ms1 = (res, ms2, s2.ffi) := by
  intro h
  obtain ⟨k, ms2, hk⟩ := compileCorrectFor_all s1 res mc s2 code2 labs t1 ms1 p h
  exact ⟨k, Classical.arbitrary T, ms2, hk⟩

end Flapjack.Compiler.Backend.LabToTarget
