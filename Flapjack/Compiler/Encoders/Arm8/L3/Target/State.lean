import Flapjack.Compiler.Encoders.Arm8.L3.Target
import Flapjack.Compiler.Encoders.Arm8.L3.Configuration
import Flapjack.Compiler.Encoders.Arm8.Configuration
import Flapjack.Compiler.Encoders.AsmProps.Target
import Flapjack.Compiler.Encoders.Arm8.Machine.TargetProof
import Flapjack.HolArb

/-!
# The L3 ARMv8 `target` record

Counterpart of CakeML's `arm8_target`
(`cakeml/compiler/encoders/arm8/arm8_targetScript.sml:349-360`), stated over
the L3 `arm8_state` carrier and the L3 `arm8_next`/`arm8_ok`/`arm8_proj`.

The record uses the exact L3 `arm8_config` carrier
(`L3/Configuration.lean`) and the rendered `arm8_next`/`arm8_ok`/`arm8_proj`:
`next = THE o NextStateARM8`, `get_pc = arm8_state_PC`,
`get_reg = \s. REG s o n2w`, `get_byte = MEM`, `state_ok = arm8_ok`,
`proj = arm8_proj`.  HOL omits `get_fp_reg` from the record literal; HOL
elaborates the literal as a chain of updates over `ARB` of the target record
(`src/datatype/record/RecordType.sml`), so the omitted field is
`(ARB : target).get_fp_reg`, and the Lean record takes that same projection of
an arbitrary whole target record.  Reviewed exact over the L3 carriers; the
`config` field's callees (`arm8_ast`/`arm8_enc` and the rendered
`EncodeBitMask`) are themselves reviewed or recorded in the manifest.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3.Target

open Flapjack Compiler.Encoders.Arm8
open Flapjack.Compiler.Encoders.Arm8.L3

local instance : Nonempty (HolAsmTarget 64 arm8_state Arm8L3Projection) :=
  ⟨{ config := arm8ConfigL3,
     next := id,
     getPc := fun _ => 0,
     getReg := fun _ _ => 0,
     getFpReg := fun _ _ => 0,
     getByte := fun _ _ => 0,
     stateOk := fun _ => true,
     proj := fun _ _ => holArb Arm8L3Projection }⟩

/-- `arm8_target` (`arm8_targetScript.sml:349-360`) over the L3 carrier. -/
@[hol "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_target_def"]
noncomputable def arm8TargetL3 : HolAsmTarget 64 arm8_state Arm8L3Projection where
  config := arm8ConfigL3
  next := arm8Next
  getPc := fun s => s.PC
  getReg := fun s n => s.REG (BitVec.ofNat 5 n)
  getFpReg := (holArb (HolAsmTarget 64 arm8_state Arm8L3Projection)).getFpReg
  getByte := fun s a => s.MEM a
  stateOk := arm8Ok
  proj := arm8Proj

/-- Projection reductions used by the target-ok proof. -/
@[simp] theorem arm8TargetL3_getPc :
    arm8TargetL3.getPc = (fun s : arm8_state => s.PC) := rfl
@[simp] theorem arm8TargetL3_getReg :
    arm8TargetL3.getReg = (fun s n => s.REG (BitVec.ofNat 5 n)) := rfl
@[simp] theorem arm8TargetL3_getFpReg : arm8TargetL3.getFpReg =
    (holArb (HolAsmTarget 64 arm8_state Arm8L3Projection)).getFpReg := rfl
@[simp] theorem arm8TargetL3_getByte :
    arm8TargetL3.getByte = (fun s a => s.MEM a) := rfl
@[simp] theorem arm8TargetL3_stateOk : arm8TargetL3.stateOk = arm8Ok := rfl
@[simp] theorem arm8TargetL3_proj : arm8TargetL3.proj = arm8Proj := rfl
@[simp] theorem arm8TargetL3_config : arm8TargetL3.config = arm8ConfigL3 := rfl

/-- Record projection regression. -/
theorem arm8TargetL3_projections :
    arm8TargetL3.next = arm8Next ∧
    arm8TargetL3.config = arm8ConfigL3 ∧
    arm8TargetL3.getPc = (fun s : arm8_state => s.PC) ∧
    arm8TargetL3.getReg = (fun s n => s.REG (BitVec.ofNat 5 n)) ∧
    arm8TargetL3.getFpReg =
      (holArb (HolAsmTarget 64 arm8_state Arm8L3Projection)).getFpReg ∧
    arm8TargetL3.getByte = (fun s a => s.MEM a) ∧
    arm8TargetL3.stateOk = arm8Ok ∧
    arm8TargetL3.proj = arm8Proj := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Projection consistency: equal projections give equal readable L3 state. -/
theorem arm8TargetL3_targetOkProjection (ms1 ms2 : arm8_state) (s : AsmState 64)
    (h : arm8Proj s.memDomain ms1 = arm8Proj s.memDomain ms2) :
    (targetStateRel arm8TargetL3 s ms1 ↔ targetStateRel arm8TargetL3 s ms2) ∧
      arm8Ok ms1 = arm8Ok ms2 ∧
      ms1.PC = ms2.PC ∧
      (∀ a, s.memDomain a → ms1.MEM a = ms2.MEM a) := by
  have hPSTATE : ms1.PSTATE = ms2.PSTATE := congrArg (fun p => p.1) h
  have hSCTLR : ms1.SCTLR_EL1 = ms2.SCTLR_EL1 := congrArg (fun p => p.2.1) h
  have hTCR : ms1.TCR_EL1 = ms2.TCR_EL1 := congrArg (fun p => p.2.2.1) h
  have hExc : ms1.exception = ms2.exception := congrArg (fun p => p.2.2.2.1) h
  have hREG : ms1.REG = ms2.REG := congrArg (fun p => p.2.2.2.2.1) h
  have hmem : (arm8Proj s.memDomain ms1).2.2.2.2.2.1 =
      (arm8Proj s.memDomain ms2).2.2.2.2.2.1 := congrArg (fun p => p.2.2.2.2.2.1) h
  have hPC : ms1.PC = ms2.PC := congrArg (fun p => p.2.2.2.2.2.2) h
  have hget (a : BitVec 64) (ha : s.memDomain a) : ms1.MEM a = ms2.MEM a := by
    have hleft : (arm8Proj s.memDomain ms1).2.2.2.2.2.1 (a, ms1.MEM a) := by
      rw [arm8Proj_memory]
      exact ⟨rfl, ha⟩
    rw [congrFun hmem (a, ms1.MEM a)] at hleft
    rw [arm8Proj_memory] at hleft
    exact hleft.1.symm
  have hok : arm8Ok ms1 = arm8Ok ms2 := by
    simp only [arm8Ok, hPSTATE, hSCTLR, hTCR, hExc, hPC]
  refine ⟨?_, hok, hPC, hget⟩
  simp only [targetStateRel, arm8TargetL3_getPc, arm8TargetL3_getReg,
    arm8TargetL3_getByte, arm8TargetL3_stateOk, arm8TargetL3_getFpReg,
    arm8TargetL3_config]
  constructor
  · intro hs
    rcases hs with ⟨hok1, hpc1, hmem1, hreg1, hfp1⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [hok] using hok1
    · simpa [hPC] using hpc1
    · intro a ha
      rw [← hget a ha]
      exact hmem1 a ha
    · intro i hi
      rw [← hREG]
      exact hreg1 i hi
    · intro i hi
      simp [arm8ConfigL3] at hi
  · intro hs
    rcases hs with ⟨hok1, hpc1, hmem1, hreg1, hfp1⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [hok] using hok1
    · simpa [hPC] using hpc1
    · intro a ha
      rw [hget a ha]
      exact hmem1 a ha
    · intro i hi
      rw [hREG]
      exact hreg1 i hi
    · intro i hi
      simp [arm8ConfigL3] at hi

/-- `target_ok` for the L3 ARMv8 target: the exact L3 configuration is `enc_ok`
and the projection determines the readable state.  This is the `targetOk`
conjunct of `encoderCorrect`, and the L3 instance of HOL's local
`arm8_target_ok`; the per-instruction cases are the tagged case theorems in
`CorrectnessEncoding` and are assembled in
`arm8EncoderCorrectL3`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_target_ok"]
theorem arm8TargetL3_targetOk : targetOk arm8TargetL3 := by
  refine ⟨arm8ConfigL3_encOk, ?_⟩
  intro ms1 ms2 s hproj
  exact arm8TargetL3_targetOkProjection ms1 ms2 s hproj

end Flapjack.Compiler.Encoders.Arm8.L3.Target
