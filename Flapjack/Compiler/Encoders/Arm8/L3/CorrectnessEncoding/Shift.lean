import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Const
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Simulate

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

/-!
# The `shift` register constructor of `encoder_correct arm8TargetL3`

`arm8_ast` lowers `Arith (Shift sh d s (Reg r))` to the single instruction
`Shift@64 (1, arm8_shv sh, r, s, d)`.  This module records the emitted word,
its `Encode`/`Decode` inverse, the `Run` semantics through `ShiftReg` /
`ShiftValue`, and the corresponding case of `encoder_correct arm8TargetL3`.

The immediate form of `shift` lowers to `BitfieldMove@64` / `ExtractRegister@64`
and is not covered here.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The word emitted for `Shift@64` (register form): HOL's `e_data` term
`0b10011011010 ++ Rm ++ 0010 ++ shift_type ++ Rn ++ Rd`
(Flapjack infrastructure: a readable abbreviation for a mechanically rendered
term). -/
def arm8ShiftWord (sh : ShiftType) (rm rn rd : BitVec 5) : BitVec 32 :=
  BitVec.setWidth 32 ((BitVec.ofNat 11 1238) ++
    BitVec.setWidth 21 (rm ++
      BitVec.setWidth 16 ((2 : BitVec 4) ++
        BitVec.setWidth 12 (BitVec.ofNat 2 (ShiftType2num sh) ++
          BitVec.setWidth 10 (rn ++ rd)))))

/-- `e_data` of `Shift@64` is the shift word (Flapjack infrastructure; no
separately named HOL declaration). -/
theorem arm8EData_shift (sh : ShiftType) (rm rn rd : BitVec 5) :
    e_data (.«Shift@64» ((1 : BitVec 64), (sh, (rm, (rn, rd))))) =
      MachineCode.ARM8 (arm8ShiftWord sh rm rn rd) := by
  rfl

/-- `Encode` of `Shift@64` is the shift word (Flapjack infrastructure; no
separately named HOL declaration). -/
theorem arm8Encode_shift (sh : ShiftType) (rm rn rd : BitVec 5) :
    Encode (.Data (.«Shift@64» ((1 : BitVec 64), (sh, (rm, (rn, rd)))))) =
      MachineCode.ARM8 (arm8ShiftWord sh rm rn rd) := by
  simp only [Encode, arm8EData_shift]

/-- Two-bit roundtrip for the `01` bit list (`lsr`). -/
theorem holV2w_two_one : holV2w 2 [false, true] = (1 : BitVec 2) := by decide

/-- The rendered `Decode` inverts `arm8ShiftWord`. -/
theorem arm8Decode_shift (sh : ShiftType) (rm rn rd : BitVec 5) :
    Decode (arm8ShiftWord sh rm rn rd) =
      instruction.Data (Data.«Shift@64» ((1 : BitVec 64), (sh, (rm, (rn, rd))))) := by
  simp only [arm8ShiftWord, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  cases sh <;>
    simp [holV2w_two_zero, holV2w_two_one, holV2w_two_two, holV2w_two_three,
      holV2w_five, DecodeShift, num2ShiftType, ShiftType2num]

/-- `Run` of `Shift@64` (register form): shift `Rn` by the register value and
write the result to `Rd`. -/
theorem arm8Run_shift (sh : ShiftType) (rm rn rd : BitVec 5) (st : arm8_state) :
    Run (instruction.Data (Data.«Shift@64» ((1 : BitVec 64), (sh, (rm, (rn, rd)))))) st =
      «write'X» (ShiftReg (TN := 64) (rn, (sh, (X (TN := 64) rm st).toNat % 64)) st, rd) st := by
  simp only [Run, «dfn'Shift»]

/-! ## The `shift` register constructor -/

/-- The `shift` register constructor of `encoder_correct arm8TargetL3`,
lowered to the single instruction `Shift@64`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_shift_reg (sh : Flapjack.Shift) (destination source right : Nat)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.arith (.shift sh destination source (.reg right)))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.arith (.shift sh destination source (.reg right)))) s1 s2 ms := by
  have hs := h.1
  have hregok : (asmRegOkExact destination arm8ConfigL3 = true ∧
      asmRegOkExact source arm8ConfigL3 = true) ∧
      asmRegOkExact right arm8ConfigL3 = true := by
    have hk := hs.2.2.2.2.2.2
    simpa [asmOkExact, asmInstOkExact, asmArithOkExact, arm8ConfigL3,
      Bool.and_eq_true] using hk
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hregok.1.1
  obtain ⟨hslt, hsav, hs31⟩ := regOk_of_asmL3 hregok.1.2
  obtain ⟨hrlt, hrav, hr31⟩ := regOk_of_asmL3 hregok.2
  have hast : arm8Ast (.inst (.arith (.shift sh destination source (.reg right)))) =
      [.Data (.«Shift@64» (1, arm8Shv sh, BitVec.ofNat 5 right, BitVec.ofNat 5 source,
        BitVec.ofNat 5 destination))] := by
    simp [arm8Ast]
  have henc : arm8Enc (.inst (.arith (.shift sh destination source (.reg right)))) =
      arm8Encode (.Data (.«Shift@64» (1, arm8Shv sh, BitVec.ofNat 5 right,
        BitVec.ofNat 5 source, BitVec.ofNat 5 destination))) := by
    rw [arm8Enc, hast]
    simp
  let w : BitVec 32 := arm8ShiftWord (arm8Shv sh) (BitVec.ofNat 5 right)
    (BitVec.ofNat 5 source) (BitVec.ofNat 5 destination)
  have hdec : Decode w = instruction.Data (Data.«Shift@64»
      ((1 : BitVec 64), (arm8Shv sh, (BitVec.ofNat 5 right, (BitVec.ofNat 5 source,
        BitVec.ofNat 5 destination))))) :=
    arm8Decode_shift (arm8Shv sh) _ _ _
  let v : BitVec 64 := wordShift sh (s1.regs source) (s1.regs right).toNat
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  have hlt_amount : (s1.regs right).toNat < 64 := by
    have hf : s2.failed = false := by simpa using hs.2.2.2.2.2.1
    rw [← hupd] at hf
    simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc] at hf
    exact hf.1
  have hamount : (s1.regs right).toNat % 64 = (s1.regs right).toNat :=
    Nat.mod_eq_of_lt hlt_amount
  refine arm8RegCaseOne _ destination v s1 s2 ms h (by omega) _ _ _ henc (by rw [arm8Encode_shift]) hdec ?_ ?_
  · intro hreg
    rw [arm8Run_shift, arm8WriteX_of_valid _ _ hd31 hdlt]
    simp only [ShiftReg, ShiftValue, arm8Shv]
    rw [arm8X_of_valid _ hs31 hslt, arm8X_of_valid _ hr31 hrlt]
    cases sh <;>
      simp [v, holUpdate, wordShift, hamount,
        hreg source ⟨hslt, hsav⟩, hreg right ⟨hrlt, hrav⟩]
  · intro hreg p
    refine ⟨?_, fun x => ?_, ?_, fun k => ?_⟩
    · simp [asmUpd, instUpd, arithUpd, updPc]
    · simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc]
    · simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc]
    · simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc, v,
        Flapjack.Compiler.Encoders.AsmSem.readReg, Flapjack.Compiler.Encoders.AsmSem.regImm]

end Flapjack.Compiler.Encoders.Arm8.L3
