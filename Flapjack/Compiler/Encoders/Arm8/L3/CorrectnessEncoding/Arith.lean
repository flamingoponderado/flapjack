import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.MoveWide
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.LogicalImmediate
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Const

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

/-!
# The `arith` constructors of `encoder_correct arm8TargetL3`

Encoding facts for the arithmetic instruction forms used by `arm8_ast`.
The `binop` case proof itself is built on these in the next layer.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The word emitted for `AddSubShiftedRegister@64`, in the shape produced by
the rendered `e_data` (Flapjack infrastructure: a readable abbreviation for a
mechanically rendered term). -/
def arm8AddSubShiftedRegisterWord (op : Bool) (s : Bool) (shift : ShiftType)
    (rm : BitVec 5) (amount : BitVec 6) (rn rd : BitVec 5) : BitVec 32 :=
  BitVec.setWidth 32 ((1 : BitVec 1) ++ BitVec.setWidth 31 (holV2w 1 [op] ++ BitVec.setWidth 30 (holV2w 1 [s] ++ BitVec.setWidth 29 ((11 : BitVec 5) ++ BitVec.setWidth 24 (BitVec.ofNat 2 (ShiftType2num shift) ++ BitVec.setWidth 22 ((0 : BitVec 1) ++ BitVec.setWidth 21 (rm ++ BitVec.setWidth 16 (amount ++ BitVec.setWidth 10 (rn ++ rd)))))))))

/-- `Encode` of `AddSubShiftedRegister@64` is the shifted-register word
(Flapjack infrastructure; no separately named HOL declaration). -/
theorem arm8Encode_addSubShiftedRegister (op : Bool) (s : Bool) (shift : ShiftType)
    (rm : BitVec 5) (amount : BitVec 6) (rn rd : BitVec 5) :
    Encode (.Data (.«AddSubShiftedRegister@64»
      ((1 : BitVec 64), (op, (s, (shift, (rm, (amount, (rn, rd))))))))) =
      MachineCode.ARM8 (arm8AddSubShiftedRegisterWord op s shift rm amount rn rd) := by
  simp only [Encode, e_data, arm8AddSubShiftedRegisterWord]
  rfl

/-- The rendered `Decode` inverts `arm8AddSubShiftedRegisterWord` for the
`lsl` shift used by `arm8_ast` (the other shifts encode other instructions,
and `ror` decodes as `Reserved`). -/
theorem arm8Decode_addSubShiftedRegister (op : Bool) (s : Bool)
    (rm : BitVec 5) (amount : BitVec 6) (rn rd : BitVec 5) :
    Decode (arm8AddSubShiftedRegisterWord op s ShiftType.lsl rm amount rn rd) =
      instruction.Data (Data.«AddSubShiftedRegister@64»
        ((1 : BitVec 64), (op, (s, (ShiftType.lsl, (rm, (amount, (rn, rd)))))))) := by
  simp only [arm8AddSubShiftedRegisterWord, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  cases op <;> cases s <;>
    simp [holV2w_one_true, holV2w_one_false, holV2w_two_zero, holV2w_five,
      holV2w_six, DecodeShift, ShiftType2num, num2ShiftType]

/-- `Run` of `AddSubShiftedRegister@64` with the `lsl` shift: add or subtract
the shifted register through `AddWithCarry`, write the result to `rd`, and
optionally set the flags. -/
theorem arm8Run_addSubShiftedRegister (op : Bool) (rm : BitVec 5) (amount : BitVec 6)
    (rn rd : BitVec 5) (st : arm8_state) :
    Run (instruction.Data (Data.«AddSubShiftedRegister@64»
      ((1 : BitVec 64), (op, (false, (ShiftType.lsl, (rm, (amount, (rn, rd))))))))) st =
      let p := if op then (~~~ShiftReg (TN := 64) (rm, ShiftType.lsl, amount.toNat) st, true)
        else (ShiftReg (TN := 64) (rm, ShiftType.lsl, amount.toNat) st, false)
      let r := AddWithCarry (X rn st, p.1, p.2)
      write'X (r.1, rd) (SetTheFlags (false, r.2) st) := by
  cases op <;>
    simp only [Run, «dfn'AddSubShiftedRegister», Bool.false_eq_true, if_true, if_false]


/-! ## The `binop` register `add`/`sub` constructors -/

/-- The `binop` register `add`/`sub` constructor of `encoder_correct arm8TargetL3`,
lowered to `AddSubShiftedRegister@64` with an `lsl` shift by zero. -/
theorem arm8_encoder_correct_binop_addsub_reg (op : Bool) (bop : HolBinop)
    (hbop : bop = if op then .sub else .add) (destination source right : Nat)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.arith (.binop bop destination source (.reg right)))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.arith (.binop bop destination source (.reg right)))) s1 s2 ms := by
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
    simpa [asmOkExact, asmInstOkExact, asmArithOkExact, asmRegImmOkExact, arm8ConfigL3,
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
      (arm8Enc (.inst (.arith (.binop bop destination source (.reg right))))) ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hdom n hn)).symm⟩
  have hast : arm8Ast (.inst (.arith (.binop bop destination source (.reg right)))) =
      [.Data (.«AddSubShiftedRegister@64»
        (1, op, false, .lsl, BitVec.ofNat 5 right, 0, BitVec.ofNat 5 source,
          BitVec.ofNat 5 destination))] := by
    cases op <;> simp [arm8Ast, hbop]
  have henc : arm8Enc (.inst (.arith (.binop bop destination source (.reg right)))) =
      arm8Encode (.Data (.«AddSubShiftedRegister@64»
        (1, op, false, .lsl, BitVec.ofNat 5 right, 0, BitVec.ofNat 5 source,
          BitVec.ofNat 5 destination))) := by
    rw [arm8Enc, hast]
    simp
  have hlen : (arm8Enc (.inst (.arith (.binop bop destination source (.reg right))))).length = 4 := by
    rw [henc]; exact arm8Encode_length _
  let w : BitVec 32 := arm8AddSubShiftedRegisterWord op false .lsl
    (BitVec.ofNat 5 right) 0 (BitVec.ofNat 5 source) (BitVec.ofNat 5 destination)
  have h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w >>> 0).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 0 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, arm8Encode_addSubShiftedRegister] at hh
    simp at hh
    simpa [w] using hh
  have h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w >>> 8).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 1 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, arm8Encode_addSubShiftedRegister] at hh
    simp at hh
    simpa [w] using hh
  have h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w >>> 16).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 2 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, arm8Encode_addSubShiftedRegister] at hh
    simp at hh
    simpa [w] using hh
  have h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w >>> 24).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 3 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, arm8Encode_addSubShiftedRegister] at hh
    simp at hh
    simpa [w] using hh
  have hdec : Decode w = instruction.Data (Data.«AddSubShiftedRegister@64»
      ((1 : BitVec 64), (op, (false, (ShiftType.lsl, (BitVec.ofNat 5 right,
        (0, (BitVec.ofNat 5 source, BitVec.ofNat 5 destination)))))))) :=
    arm8Decode_addSubShiftedRegister op false _ _ _ _
  let v : BitVec 64 := if op then
      ms.REG (BitVec.ofNat 5 source) - ms.REG (BitVec.ofNat 5 right)
    else ms.REG (BitVec.ofNat 5 source) + ms.REG (BitVec.ofNat 5 right)
  have hbr : (Run (instruction.Data (Data.«AddSubShiftedRegister@64»
      ((1 : BitVec 64), (op, (false, (ShiftType.lsl, (BitVec.ofNat 5 right,
        (0, (BitVec.ofNat 5 source, BitVec.ofNat 5 destination)))))))))
      { ms with branch_hint := none }).branch_hint = none := by
    rw [arm8Run_addSubShiftedRegister]
    cases op <;>
      simp only [SetTheFlags, Bool.false_eq_true, if_false, if_true, «write'X»] <;>
      split <;> rfl
  have hexc : (Run (instruction.Data (Data.«AddSubShiftedRegister@64»
      ((1 : BitVec 64), (op, (false, (ShiftType.lsl, (BitVec.ofNat 5 right,
        (0, (BitVec.ofNat 5 source, BitVec.ofNat 5 destination)))))))))
      { ms with branch_hint := none }).exception = exception.NoException := by
    rw [arm8Run_addSubShiftedRegister]
    cases op <;>
      simp only [SetTheFlags, Bool.false_eq_true, if_false, if_true, «write'X»] <;>
      split <;> simpa using hexc0
  have hn := arm8Next_word ms w
    (instruction.Data (Data.«AddSubShiftedRegister@64»
      ((1 : BitVec 64), (op, (false, (ShiftType.lsl, (BitVec.ofNat 5 right,
        (0, (BitVec.ofNat 5 source, BitVec.ofNat 5 destination)))))))))
    hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  have hrun : Run (instruction.Data (Data.«AddSubShiftedRegister@64»
      ((1 : BitVec 64), (op, (false, (ShiftType.lsl, (BitVec.ofNat 5 right,
        (0, (BitVec.ofNat 5 source, BitVec.ofNat 5 destination)))))))))
      { ms with branch_hint := none } =
      { ms with branch_hint := none, REG := holUpdate (BitVec.ofNat 5 destination) v ms.REG } := by
    rw [arm8Run_addSubShiftedRegister]
    cases op
    · simp only [SetTheFlags, Bool.false_eq_true, if_false, ShiftReg, ShiftValue]
      rw [arm8WriteX_of_valid _ _ hd31 hdlt, arm8X_of_valid _ hs31 hslt, arm8X_of_valid _ hr31 hrlt]
      simp [arm8AddWithCarry_add, holUpdate, v]
    · simp only [SetTheFlags, Bool.false_eq_true, if_false, ShiftReg, ShiftValue]
      rw [arm8WriteX_of_valid _ _ hd31 hdlt, arm8X_of_valid _ hs31 hslt, arm8X_of_valid _ hr31 hrlt]
      simp [arm8AddWithCarry_sub, holUpdate, v]
  have hnext : arm8Next ms = { ms with branch_hint := none, REG := holUpdate (BitVec.ofNat 5 destination) v ms.REG, PC := ms.PC + 4 } := by
    unfold arm8Next
    rw [hn, hrun]
    rfl
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  rw [hlen] at hupd
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 4 := by
    rw [← hupd]; simp [asmUpd, instUpd, arithUpd, updPc]
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    intro x; rw [← hupd]; simp [asmUpd, instUpd, arithUpd, binopUpd, updReg, updPc]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]; simp [asmUpd, instUpd, arithUpd, binopUpd, updReg, updPc]
  have hs2regs : ∀ k, s2.regs k = if k = destination then v else s1.regs k := by
    intro k
    rw [← hupd]
    cases op
    · simp [asmUpd, instUpd, arithUpd, binopUpd, updReg, updPc, hbop, v,
        Flapjack.Compiler.Encoders.AsmSem.readReg, Flapjack.Compiler.Encoders.AsmSem.regImm,
        hreg source ⟨hslt, hsav⟩, hreg right ⟨hrlt, hrav⟩]
    · simp [asmUpd, instUpd, arithUpd, binopUpd, updReg, updPc, hbop, v,
        Flapjack.Compiler.Encoders.AsmSem.readReg, Flapjack.Compiler.Encoders.AsmSem.regImm,
        hreg source ⟨hslt, hsav⟩, hreg right ⟨hrlt, hrav⟩]
  refine asmCaseOne (.arith (.binop bop destination source (.reg right))) destination v
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


