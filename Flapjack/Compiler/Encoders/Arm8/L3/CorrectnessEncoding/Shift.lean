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
  obtain ⟨hs, hr⟩ := h
  obtain ⟨hok, hpc, hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change ms.PC = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.MEM a = s1.mem a at hmem
  change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
    ms.REG (BitVec.ofNat 5 k) = s1.regs k at hreg
  have hregok : (asmRegOkExact destination arm8ConfigL3 = true ∧
      asmRegOkExact source arm8ConfigL3 = true) ∧
      asmRegOkExact right arm8ConfigL3 = true := by
    have hk := hs.2.2.2.2.2.2
    simpa [asmOkExact, asmInstOkExact, asmArithOkExact, arm8ConfigL3,
      Bool.and_eq_true] using hk
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hregok.1.1
  obtain ⟨hslt, hsav, hs31⟩ := regOk_of_asmL3 hregok.1.2
  obtain ⟨hrlt, hrav, hr31⟩ := regOk_of_asmL3 hregok.2
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC
      (arm8Enc (.inst (.arith (.shift sh destination source (.reg right))))) ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hdom n hn)).symm⟩
  have hast : arm8Ast (.inst (.arith (.shift sh destination source (.reg right)))) =
      [.Data (.«Shift@64» (1, arm8Shv sh, BitVec.ofNat 5 right, BitVec.ofNat 5 source,
        BitVec.ofNat 5 destination))] := by
    simp [arm8Ast]
  have henc : arm8Enc (.inst (.arith (.shift sh destination source (.reg right)))) =
      arm8Encode (.Data (.«Shift@64» (1, arm8Shv sh, BitVec.ofNat 5 right,
        BitVec.ofNat 5 source, BitVec.ofNat 5 destination))) := by
    rw [arm8Enc, hast]
    simp
  have hlen : (arm8Enc (.inst (.arith (.shift sh destination source (.reg right))))).length = 4 := by
    rw [henc]; exact arm8Encode_length _
  let w : BitVec 32 := arm8ShiftWord (arm8Shv sh) (BitVec.ofNat 5 right)
    (BitVec.ofNat 5 source) (BitVec.ofNat 5 destination)
  have h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w >>> 0).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 0 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, arm8Encode_shift] at hh
    simp at hh
    simpa [w] using hh
  have h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w >>> 8).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 1 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, arm8Encode_shift] at hh
    simp at hh
    simpa [w] using hh
  have h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w >>> 16).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 2 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, arm8Encode_shift] at hh
    simp at hh
    simpa [w] using hh
  have h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w >>> 24).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 3 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, arm8Encode_shift] at hh
    simp at hh
    simpa [w] using hh
  have hdec : Decode w = instruction.Data (Data.«Shift@64»
      ((1 : BitVec 64), (arm8Shv sh, (BitVec.ofNat 5 right, (BitVec.ofNat 5 source,
        BitVec.ofNat 5 destination))))) :=
    arm8Decode_shift (arm8Shv sh) _ _ _
  let v : BitVec 64 := wordShift sh (s1.regs source) (s1.regs right).toNat
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  rw [hlen] at hupd
  have hlt_amount : (s1.regs right).toNat < 64 := by
    have hf : s2.failed = false := by simpa using hs.2.2.2.2.2.1
    rw [← hupd] at hf
    simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc] at hf
    exact hf.1
  have hamount : (s1.regs right).toNat % 64 = (s1.regs right).toNat :=
    Nat.mod_eq_of_lt hlt_amount
  have hbr : (Run (instruction.Data (Data.«Shift@64»
      ((1 : BitVec 64), (arm8Shv sh, (BitVec.ofNat 5 right, (BitVec.ofNat 5 source,
        BitVec.ofNat 5 destination)))))) { ms with branch_hint := none }).branch_hint = none := by
    rw [arm8Run_shift, arm8WriteX_of_valid _ _ hd31 hdlt]
  have hexc : (Run (instruction.Data (Data.«Shift@64»
      ((1 : BitVec 64), (arm8Shv sh, (BitVec.ofNat 5 right, (BitVec.ofNat 5 source,
        BitVec.ofNat 5 destination)))))) { ms with branch_hint := none }).exception =
      exception.NoException := by
    rw [arm8Run_shift, arm8WriteX_of_valid _ _ hd31 hdlt]
    simpa using hexc0
  have hn := arm8Next_word ms w
    (instruction.Data (Data.«Shift@64»
      ((1 : BitVec 64), (arm8Shv sh, (BitVec.ofNat 5 right, (BitVec.ofNat 5 source,
        BitVec.ofNat 5 destination))))))
    hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  have hrun : Run (instruction.Data (Data.«Shift@64»
      ((1 : BitVec 64), (arm8Shv sh, (BitVec.ofNat 5 right, (BitVec.ofNat 5 source,
        BitVec.ofNat 5 destination)))))) { ms with branch_hint := none } =
      { ms with branch_hint := none, REG := holUpdate (BitVec.ofNat 5 destination) v ms.REG } := by
    rw [arm8Run_shift, arm8WriteX_of_valid _ _ hd31 hdlt]
    simp only [ShiftReg, ShiftValue, arm8Shv]
    rw [arm8X_of_valid _ hs31 hslt, arm8X_of_valid _ hr31 hrlt]
    cases sh <;>
      simp [v, holUpdate, wordShift, hamount,
        hreg source ⟨hslt, hsav⟩, hreg right ⟨hrlt, hrav⟩]
  have hnext : arm8Next ms = { ms with branch_hint := none, REG := holUpdate (BitVec.ofNat 5 destination) v ms.REG, PC := ms.PC + 4 } := by
    unfold arm8Next
    rw [hn, hrun]
    rfl
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 4 := by
    rw [← hupd]; simp [asmUpd, instUpd, arithUpd, updPc]
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    intro x; rw [← hupd]; simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]; simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc]
  have hs2regs : ∀ k, s2.regs k = if k = destination then v else s1.regs k := by
    intro k
    rw [← hupd]
    simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc, v,
      Flapjack.Compiler.Encoders.AsmSem.readReg, Flapjack.Compiler.Encoders.AsmSem.regImm]
  refine asmCaseOne (.arith (.shift sh destination source (.reg right))) destination v
    _ s1 s2 ms ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ hnext ?_ ?_ ?_ ?_ ?_ hs2pc hs2mem hs2dom hs2regs
  · rfl
  · intro x; rfl
  · intro k hk hkne
    show (if (BitVec.ofNat 5 destination) = (BitVec.ofNat 5 k) then v
      else ms.REG (BitVec.ofNat 5 k)) = ms.REG (BitVec.ofNat 5 k)
    rw [if_neg]
    intro hh
    apply hkne
    have := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    have hd32 : destination % 2 ^ 5 = destination := Nat.mod_eq_of_lt (by omega)
    have hk32 : k % 2 ^ 5 = k := Nat.mod_eq_of_lt (by omega)
    omega
  · show (if (BitVec.ofNat 5 destination) = (BitVec.ofNat 5 destination) then v
      else ms.REG (BitVec.ofNat 5 destination)) = v
    rw [if_pos rfl]
  · rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, ?_⟩
    have h4 : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
    have hal4 : holAligned 2 (ms.PC + 4) = true := by
      rw [(alignedAddSub 2 ms.PC 4 h4).1, halign]
    change holAligned 2 (ms.PC + 4) = true
    exact hal4

end Flapjack.Compiler.Encoders.Arm8.L3
