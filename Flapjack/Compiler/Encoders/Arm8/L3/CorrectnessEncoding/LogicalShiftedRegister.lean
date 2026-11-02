import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Const

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

/-!
# `LogicalShiftedRegister@64`: the word, `Encode`, `Decode` and `Run`

The `binop` `and`/`or`/`xor` forms of `arm8_ast` are lowered to a
`LogicalShiftedRegister@64` with `sf = 1`, no inversion, no flag setting, an
`lsl` shift by zero.  This module records the emitted word and the semantic
facts the encoder-correctness case needs.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The word emitted for `LogicalShiftedRegister@64`, in the shape produced by
the rendered `e_data` (Flapjack infrastructure: a readable abbreviation for a
mechanically rendered term). -/
def arm8LogicalShiftedRegisterWord (opc : BitVec 2) (invert : Bool) (sh : ShiftType)
    (imm : Nat) (rm rn rd : BitVec 5) : BitVec 32 :=
  BitVec.setWidth 32 ((1 : BitVec 1) ++
    BitVec.setWidth 31 (opc ++
      BitVec.setWidth 29 ((10 : BitVec 5) ++
        BitVec.setWidth 24 (BitVec.ofNat 2 (ShiftType2num sh) ++
          BitVec.setWidth 22 (holV2w 1 [invert] ++
            BitVec.setWidth 21 (rm ++
              BitVec.setWidth 16 (BitVec.ofNat 6 imm ++
                BitVec.setWidth 10 (rn ++ rd))))))))

/-- `Encode` of the `AND` lowering is the documented word. -/
theorem arm8Encode_logicalShiftedRegister_and (rm rn rd : BitVec 5) :
    Encode (.Data (.«LogicalShiftedRegister@64»
      ((1 : BitVec 64), (.LogicalOp_AND, (false, (false, (ShiftType.lsl,
        (0, (rm, (rn, rd)))))))))) =
      MachineCode.ARM8 (arm8LogicalShiftedRegisterWord (0 : BitVec 2) false .lsl 0 rm rn rd) := by
  rfl

/-- `Encode` of the `ORR` lowering is the documented word. -/
theorem arm8Encode_logicalShiftedRegister_orr (rm rn rd : BitVec 5) :
    Encode (.Data (.«LogicalShiftedRegister@64»
      ((1 : BitVec 64), (.LogicalOp_ORR, (false, (false, (ShiftType.lsl,
        (0, (rm, (rn, rd)))))))))) =
      MachineCode.ARM8 (arm8LogicalShiftedRegisterWord (1 : BitVec 2) false .lsl 0 rm rn rd) := by
  rfl

/-- `Encode` of the `EOR` lowering is the documented word. -/
theorem arm8Encode_logicalShiftedRegister_eor (rm rn rd : BitVec 5) :
    Encode (.Data (.«LogicalShiftedRegister@64»
      ((1 : BitVec 64), (.LogicalOp_EOR, (false, (false, (ShiftType.lsl,
        (0, (rm, (rn, rd)))))))))) =
      MachineCode.ARM8 (arm8LogicalShiftedRegisterWord (2 : BitVec 2) false .lsl 0 rm rn rd) := by
  rfl


/-- The one-bit `false` list is the zero word (bit-list roundtrip helper). -/
theorem arm8HolV2w_one_false : holV2w 1 [false] = (0 : BitVec 1) := by decide

/-- The one-bit `true` list is the one word (bit-list roundtrip helper). -/
theorem arm8HolV2w_one_true : holV2w 1 [true] = (1 : BitVec 1) := by decide

/-- Six `false` bits are the zero six-bit word (bit-list roundtrip helper). -/
theorem arm8HolV2w_six_zero :
    holV2w 6 [false, false, false, false, false, false] = (0 : BitVec 6) := by decide

/-- The rendered `Decode` inverts `arm8LogicalShiftedRegisterWord` for the
flag-preserving, non-inverting `lsl`-by-zero form. -/
theorem arm8Decode_logicalShiftedRegister (opc : LogicalOp) (opcbits : BitVec 2)
    (hdec : DecodeLogicalOp opcbits = (opc, false)) (invert : Bool) (rm rn rd : BitVec 5) :
    Decode (arm8LogicalShiftedRegisterWord opcbits invert .lsl 0 rm rn rd) =
      instruction.Data (Data.«LogicalShiftedRegister@64»
        ((1 : BitVec 64), (opc, (invert, (false, (ShiftType.lsl,
          (0, (rm, (rn, rd))))))))) := by
  simp only [arm8LogicalShiftedRegisterWord, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  cases invert <;>
    simp [holV2w_two, holV2w_two_zero, holV2w_five, arm8HolV2w_one_false,
      arm8HolV2w_one_true, arm8HolV2w_six_zero, hdec, DecodeShift, num2ShiftType,
      ShiftType2num]


/-- `Run` of the flag-preserving, non-inverting `LogicalShiftedRegister@64`
with an `lsl` shift by zero: combine `rn` and `rm` with the operation and write
the result to `rd`, leaving every other field unchanged. -/
theorem arm8Run_logicalShiftedRegister (opc : LogicalOp) (rm rn rd : BitVec 5)
    (st : arm8_state) :
    Run (instruction.Data (Data.«LogicalShiftedRegister@64»
      ((1 : BitVec 64), (opc, (false, (false, (ShiftType.lsl, (0, (rm, (rn, rd)))))))))) st =
      write'X ((match opc with
        | .LogicalOp_AND => X (TN := 64) rn st &&& X (TN := 64) rm st
        | .LogicalOp_ORR => X (TN := 64) rn st ||| X (TN := 64) rm st
        | .LogicalOp_EOR => X (TN := 64) rn st ^^^ X (TN := 64) rm st), rd) st := by
  simp only [Run, «dfn'LogicalShiftedRegister», SetTheFlags, ShiftReg, ShiftValue,
    BitVec.shiftLeft_zero, Bool.false_eq_true, if_false]
  rfl


/-! ## The `binop` `and`/`or`/`xor` register constructor -/

/-- The opcode bits `EncodeLogicalOp` emits for the three `arm8_ast` `binop`
operations that use `LogicalShiftedRegister@64`. -/
def arm8BopOpcBits (bop : HolBinop) : BitVec 2 :=
  match bop with
  | .and => (0 : BitVec 2)
  | .or => (1 : BitVec 2)
  | .xor => (2 : BitVec 2)
  | _ => (0 : BitVec 2)

/-- The `binop` register `and`/`or`/`xor` constructor of
`encoder_correct arm8TargetL3`, lowered to `LogicalShiftedRegister@64` with an
`lsl` shift by zero and no flag setting. -/
theorem arm8_encoder_correct_binop_logic_reg (bop : HolBinop)
    (hbop : bop = .and ∨ bop = .or ∨ bop = .xor) (destination source right : Nat)
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
      [.Data (.«LogicalShiftedRegister@64»
        (1, arm8BopEnc bop, false, false, .lsl, 0, BitVec.ofNat 5 right,
          BitVec.ofNat 5 source, BitVec.ofNat 5 destination))] := by
    rcases hbop with h | h | h <;> subst h <;> simp [arm8Ast]
  have henc : arm8Enc (.inst (.arith (.binop bop destination source (.reg right)))) =
      arm8Encode (.Data (.«LogicalShiftedRegister@64»
        (1, arm8BopEnc bop, false, false, .lsl, 0, BitVec.ofNat 5 right,
          BitVec.ofNat 5 source, BitVec.ofNat 5 destination))) := by
    rw [arm8Enc, hast]
    simp
  have hlen : (arm8Enc (.inst (.arith (.binop bop destination source (.reg right))))).length = 4 := by
    rw [henc]; exact arm8Encode_length _
  let w : BitVec 32 := arm8LogicalShiftedRegisterWord (arm8BopOpcBits bop) false .lsl 0
    (BitVec.ofNat 5 right) (BitVec.ofNat 5 source) (BitVec.ofNat 5 destination)
  have hword : Encode (.Data (.«LogicalShiftedRegister@64»
        (1, arm8BopEnc bop, false, false, .lsl, 0, BitVec.ofNat 5 right,
          BitVec.ofNat 5 source, BitVec.ofNat 5 destination))) = MachineCode.ARM8 w := by
    rcases hbop with h | h | h
    · subst h; exact arm8Encode_logicalShiftedRegister_and _ _ _
    · subst h; exact arm8Encode_logicalShiftedRegister_orr _ _ _
    · subst h; exact arm8Encode_logicalShiftedRegister_eor _ _ _
  have h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w >>> 0).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 0 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode] at hh
    rw [hword] at hh
    simp at hh
    simpa [w] using hh
  have h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w >>> 8).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 1 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode] at hh
    rw [hword] at hh
    simp at hh
    simpa [w] using hh
  have h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w >>> 16).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 2 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode] at hh
    rw [hword] at hh
    simp at hh
    simpa [w] using hh
  have h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w >>> 24).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 3 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode] at hh
    rw [hword] at hh
    simp at hh
    simpa [w] using hh
  have hdecbits : DecodeLogicalOp (arm8BopOpcBits bop) = (arm8BopEnc bop, false) := by
    rcases hbop with h | h | h <;> subst h <;> decide
  have hdec : Decode w = instruction.Data (Data.«LogicalShiftedRegister@64»
      ((1 : BitVec 64), (arm8BopEnc bop, (false, (false, (ShiftType.lsl, (0,
        (BitVec.ofNat 5 right, (BitVec.ofNat 5 source, BitVec.ofNat 5 destination))))))))) :=
    arm8Decode_logicalShiftedRegister (arm8BopEnc bop) (arm8BopOpcBits bop) hdecbits false _ _ _
  let v : BitVec 64 := match bop with
    | .and => ms.REG (BitVec.ofNat 5 source) &&& ms.REG (BitVec.ofNat 5 right)
    | .or => ms.REG (BitVec.ofNat 5 source) ||| ms.REG (BitVec.ofNat 5 right)
    | .xor => ms.REG (BitVec.ofNat 5 source) ^^^ ms.REG (BitVec.ofNat 5 right)
    | _ => 0
  have hbr : (Run (instruction.Data (Data.«LogicalShiftedRegister@64»
      ((1 : BitVec 64), (arm8BopEnc bop, (false, (false, (ShiftType.lsl, (0,
        (BitVec.ofNat 5 right, (BitVec.ofNat 5 source, BitVec.ofNat 5 destination))))))))))
      { ms with branch_hint := none }).branch_hint = none := by
    rw [arm8Run_logicalShiftedRegister]
    simp only [«write'X»]
    split <;> rfl
  have hexc : (Run (instruction.Data (Data.«LogicalShiftedRegister@64»
      ((1 : BitVec 64), (arm8BopEnc bop, (false, (false, (ShiftType.lsl, (0,
        (BitVec.ofNat 5 right, (BitVec.ofNat 5 source, BitVec.ofNat 5 destination))))))))))
      { ms with branch_hint := none }).exception = exception.NoException := by
    rw [arm8Run_logicalShiftedRegister]
    simp only [«write'X»]
    split <;> simpa using hexc0
  have hn := arm8Next_word ms w
    (instruction.Data (Data.«LogicalShiftedRegister@64»
      ((1 : BitVec 64), (arm8BopEnc bop, (false, (false, (ShiftType.lsl, (0,
        (BitVec.ofNat 5 right, (BitVec.ofNat 5 source, BitVec.ofNat 5 destination))))))))))
    hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  have hrun : Run (instruction.Data (Data.«LogicalShiftedRegister@64»
      ((1 : BitVec 64), (arm8BopEnc bop, (false, (false, (ShiftType.lsl, (0,
        (BitVec.ofNat 5 right, (BitVec.ofNat 5 source, BitVec.ofNat 5 destination))))))))))
      { ms with branch_hint := none } =
      { ms with branch_hint := none, REG := holUpdate (BitVec.ofNat 5 destination) v ms.REG } := by
    rw [arm8Run_logicalShiftedRegister]
    rw [arm8WriteX_of_valid _ _ hd31 hdlt]
    rcases hbop with h | h | h
    · subst h; simp [v, arm8BopEnc, holUpdate, arm8X_of_valid _ hs31 hslt, arm8X_of_valid _ hr31 hrlt]
    · subst h; simp [v, arm8BopEnc, holUpdate, arm8X_of_valid _ hs31 hslt, arm8X_of_valid _ hr31 hrlt]
    · subst h; simp [v, arm8BopEnc, holUpdate, arm8X_of_valid _ hs31 hslt, arm8X_of_valid _ hr31 hrlt]
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
    rcases hbop with h | h | h
    · subst h; simp [asmUpd, instUpd, arithUpd, binopUpd, updReg, updPc, v,
        Flapjack.Compiler.Encoders.AsmSem.readReg, Flapjack.Compiler.Encoders.AsmSem.regImm,
        hreg source ⟨hslt, hsav⟩, hreg right ⟨hrlt, hrav⟩]
    · subst h; simp [asmUpd, instUpd, arithUpd, binopUpd, updReg, updPc, v,
        Flapjack.Compiler.Encoders.AsmSem.readReg, Flapjack.Compiler.Encoders.AsmSem.regImm,
        hreg source ⟨hslt, hsav⟩, hreg right ⟨hrlt, hrav⟩]
    · subst h; simp [asmUpd, instUpd, arithUpd, binopUpd, updReg, updPc, v,
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


/-- `Run` of the inverted, flag-preserving `LogicalShiftedRegister@64` with an
`lsl` shift by zero: combine `rn` with the complement of `rm` and write the
result to `rd`. -/
theorem arm8Run_logicalShiftedRegister_inv (opc : LogicalOp) (rm rn rd : BitVec 5)
    (st : arm8_state) :
    Run (instruction.Data (Data.«LogicalShiftedRegister@64»
      ((1 : BitVec 64), (opc, (true, (false, (ShiftType.lsl, (0, (rm, (rn, rd)))))))))) st =
      write'X ((match opc with
        | .LogicalOp_AND => X (TN := 64) rn st &&& ~~~X (TN := 64) rm st
        | .LogicalOp_ORR => X (TN := 64) rn st ||| ~~~X (TN := 64) rm st
        | .LogicalOp_EOR => X (TN := 64) rn st ^^^ ~~~X (TN := 64) rm st), rd) st := by
  simp only [Run, «dfn'LogicalShiftedRegister», SetTheFlags, ShiftReg, ShiftValue,
    BitVec.shiftLeft_zero, Bool.false_eq_true, if_true, if_false]
  rfl

/-- `Encode` of the inverted-`ORR`-against-zero-register lowering is the
documented word. -/
theorem arm8Encode_logicalShiftedRegister_xor_neg (rm rd : BitVec 5) :
    Encode (.Data (.«LogicalShiftedRegister@64»
      ((1 : BitVec 64), (.LogicalOp_ORR, (true, (false, (ShiftType.lsl,
        (0, (rm, (31#5, rd)))))))))) =
      MachineCode.ARM8 (arm8LogicalShiftedRegisterWord (1 : BitVec 2) true .lsl 0 rm 31#5 rd) := by
  rfl

/-- `X` of the zero register is zero. -/
theorem arm8X_zero (st : arm8_state) : X (TN := 64) 31#5 st = (0 : BitVec 64) := by
  simp [X]

/-- The `binop` `Xor` immediate `-1` constructor of `encoder_correct
arm8TargetL3`, lowered to the inverted `ORR` against the zero register. -/
theorem arm8_encoder_correct_binop_xor_neg (destination source : Nat) (value : BitVec 64)
    (hneg : value = -1) (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.arith (.binop .xor destination source (.imm value)))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.arith (.binop .xor destination source (.imm value)))) s1 s2 ms := by
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
  have hokinst : asmOkExact (.inst (.arith (.binop .xor destination source (.imm value))))
      arm8ConfigL3 = true := hs.2.2.2.2.2.2
  have hregok : (asmRegOkExact destination arm8ConfigL3 = true ∧
      asmRegOkExact source arm8ConfigL3 = true) ∧
      asmRegImmOkExact (.inl .xor) (.imm value) arm8ConfigL3 = true := by
    simpa [asmOkExact, asmInstOkExact, asmArithOkExact, arm8ConfigL3,
      Bool.and_eq_true] using hokinst
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hregok.1.1
  obtain ⟨hslt, hsav, hs31⟩ := regOk_of_asmL3 hregok.1.2
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC
      (arm8Enc (.inst (.arith (.binop .xor destination source (.imm value))))) ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hdom n hn)).symm⟩
  have hast : arm8Ast (.inst (.arith (.binop .xor destination source (.imm value)))) =
      [.Data (.«LogicalShiftedRegister@64»
        (1, .LogicalOp_ORR, true, false, .lsl, 0, BitVec.ofNat 5 source, 31#5,
          BitVec.ofNat 5 destination))] := by
    simp [arm8Ast, hneg]
  have henc : arm8Enc (.inst (.arith (.binop .xor destination source (.imm value)))) =
      arm8Encode (.Data (.«LogicalShiftedRegister@64»
        (1, .LogicalOp_ORR, true, false, .lsl, 0, BitVec.ofNat 5 source, 31#5,
          BitVec.ofNat 5 destination))) := by
    rw [arm8Enc, hast]
    simp
  have hlen : (arm8Enc (.inst (.arith (.binop .xor destination source (.imm value))))).length = 4 := by
    rw [henc]; exact arm8Encode_length _
  let w : BitVec 32 := arm8LogicalShiftedRegisterWord (1 : BitVec 2) true .lsl 0
    (BitVec.ofNat 5 source) 31#5 (BitVec.ofNat 5 destination)
  have hword : Encode (.Data (.«LogicalShiftedRegister@64»
        (1, .LogicalOp_ORR, true, false, .lsl, 0, BitVec.ofNat 5 source, 31#5,
          BitVec.ofNat 5 destination))) = MachineCode.ARM8 w :=
    arm8Encode_logicalShiftedRegister_xor_neg _ _
  have h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w >>> 0).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 0 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode] at hh
    rw [hword] at hh
    simp at hh
    simpa [w] using hh
  have h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w >>> 8).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 1 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode] at hh
    rw [hword] at hh
    simp at hh
    simpa [w] using hh
  have h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w >>> 16).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 2 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode] at hh
    rw [hword] at hh
    simp at hh
    simpa [w] using hh
  have h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w >>> 24).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 3 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode] at hh
    rw [hword] at hh
    simp at hh
    simpa [w] using hh
  have hdecbits : DecodeLogicalOp (1 : BitVec 2) = (.LogicalOp_ORR, false) := by decide
  have hdec : Decode w = instruction.Data (Data.«LogicalShiftedRegister@64»
      ((1 : BitVec 64), (.LogicalOp_ORR, (true, (false, (ShiftType.lsl, (0,
        (BitVec.ofNat 5 source, (31#5, BitVec.ofNat 5 destination))))))))) :=
    arm8Decode_logicalShiftedRegister .LogicalOp_ORR (1 : BitVec 2) hdecbits true _ _ _
  let v : BitVec 64 := ~~~ms.REG (BitVec.ofNat 5 source)
  have hbr : (Run (instruction.Data (Data.«LogicalShiftedRegister@64»
      ((1 : BitVec 64), (.LogicalOp_ORR, (true, (false, (ShiftType.lsl, (0,
        (BitVec.ofNat 5 source, (31#5, BitVec.ofNat 5 destination))))))))))
      { ms with branch_hint := none }).branch_hint = none := by
    rw [arm8Run_logicalShiftedRegister_inv]
    simp only [«write'X»]
    split <;> rfl
  have hexc : (Run (instruction.Data (Data.«LogicalShiftedRegister@64»
      ((1 : BitVec 64), (.LogicalOp_ORR, (true, (false, (ShiftType.lsl, (0,
        (BitVec.ofNat 5 source, (31#5, BitVec.ofNat 5 destination))))))))))
      { ms with branch_hint := none }).exception = exception.NoException := by
    rw [arm8Run_logicalShiftedRegister_inv]
    simp only [«write'X»]
    split <;> simpa using hexc0
  have hn := arm8Next_word ms w
    (instruction.Data (Data.«LogicalShiftedRegister@64»
      ((1 : BitVec 64), (.LogicalOp_ORR, (true, (false, (ShiftType.lsl, (0,
        (BitVec.ofNat 5 source, (31#5, BitVec.ofNat 5 destination))))))))))
    hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  have hrun : Run (instruction.Data (Data.«LogicalShiftedRegister@64»
      ((1 : BitVec 64), (.LogicalOp_ORR, (true, (false, (ShiftType.lsl, (0,
        (BitVec.ofNat 5 source, (31#5, BitVec.ofNat 5 destination))))))))))
      { ms with branch_hint := none } =
      { ms with branch_hint := none, REG := holUpdate (BitVec.ofNat 5 destination) v ms.REG } := by
    rw [arm8Run_logicalShiftedRegister_inv]
    rw [arm8WriteX_of_valid _ _ hd31 hdlt]
    simp [v, holUpdate, arm8X_zero, BitVec.zero_or, arm8X_of_valid _ hs31 hslt]
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
    simp only [asmUpd, instUpd, arithUpd, binopUpd, updReg, updPc, v, hneg,
      Flapjack.Compiler.Encoders.AsmSem.readReg, Flapjack.Compiler.Encoders.AsmSem.regImm,
      hreg source ⟨hslt, hsav⟩]
    by_cases hk : k = destination
    · rw [if_pos hk, if_pos hk]
      exact BitVec.xor_allOnes
    · rw [if_neg hk, if_neg hk]
  refine asmCaseOne (.arith (.binop .xor destination source (.imm value))) destination v
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
