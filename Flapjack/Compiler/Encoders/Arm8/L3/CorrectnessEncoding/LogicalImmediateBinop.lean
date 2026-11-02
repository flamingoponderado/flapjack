import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Const
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.LogicalImmediate
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.LogicalShiftedRegister

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

/-!
# The `binop` immediate `and`/`or` constructors of `encoder_correct arm8TargetL3`

`arm8_ast` lowers `And`/`Or` with an immediate operand to
`LogicalImmediate@64 (1, opc, false, imm, rn, rd)`.  This module records the
`Run` equation for that form and assembles the encoder-correctness case.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- `Run` of the flag-preserving `LogicalImmediate@64` writes the combined word
to `rd`, leaving every other field unchanged (for `rd ≠ 31`). -/
theorem arm8Run_logicalImmediate (opc : LogicalOp) (imm : BitVec 64) (rn rd : BitVec 5)
    (st : arm8_state) (hrd : rd ≠ 31) :
    Run (instruction.Data (Data.«LogicalImmediate@64» (1, opc, false, imm, rn, rd))) st =
      write'X ((match opc with
        | .LogicalOp_AND => X (TN := 64) rn st &&& imm
        | .LogicalOp_ORR => X (TN := 64) rn st ||| imm
        | .LogicalOp_EOR => X (TN := 64) rn st ^^^ imm), rd) st := by
  simp only [Run, «dfn'LogicalImmediate», SetTheFlags, Bool.false_eq_true, if_false]
  rw [if_neg]
  · rfl
  · simpa using hrd

/-- The `binop` immediate `and`/`or` constructor of `encoder_correct
arm8TargetL3`, lowered to `LogicalImmediate@64` with no flag setting. -/
theorem arm8_encoder_correct_binop_logic_imm (bop : HolBinop)
    (hbop : bop = .and ∨ bop = .or) (destination source : Nat) (value : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.arith (.binop bop destination source (.imm value)))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.arith (.binop bop destination source (.imm value)))) s1 s2 ms := by
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
  have hokinst : asmOkExact (.inst (.arith (.binop bop destination source (.imm value))))
      arm8ConfigL3 = true := hs.2.2.2.2.2.2
  have hregok : (asmRegOkExact destination arm8ConfigL3 = true ∧
      asmRegOkExact source arm8ConfigL3 = true) ∧
      asmRegImmOkExact (.inl bop) (.imm value) arm8ConfigL3 = true := by
    simpa [asmOkExact, asmInstOkExact, asmArithOkExact, arm8ConfigL3,
      Bool.and_eq_true] using hokinst
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hregok.1.1
  obtain ⟨hslt, hsav, hs31⟩ := regOk_of_asmL3 hregok.1.2
  have hvalid : arm8ValidImmediate (.inl bop) value = true := by
    have hv := hregok.2
    rcases hbop with hb | hb
    · subst hb
      have hne : ((Sum.inl BinOp.and : Sum BinOp Cmp) == (Sum.inl BinOp.xor : Sum BinOp Cmp)) = false := by decide
      simpa [asmRegImmOkExact, arm8ConfigL3, arm8ValidImmediate, hne] using hv
    · subst hb
      have hne : ((Sum.inl BinOp.or : Sum BinOp Cmp) == (Sum.inl BinOp.xor : Sum BinOp Cmp)) = false := by decide
      simpa [asmRegImmOkExact, arm8ConfigL3, arm8ValidImmediate, hne] using hv
  obtain ⟨N, imms, immr, hbm⟩ : ∃ N imms immr, EncodeBitMask value = some (N, (imms, immr)) := by
    rcases hbop with hb | hb
    · subst hb
      simp [arm8ValidImmediate] at hvalid
      cases hb : EncodeBitMask value with
      | none => simp [hb] at hvalid
      | some p => obtain ⟨N, ⟨imms, immr⟩⟩ := p; exact ⟨N, imms, immr, rfl⟩
    · subst hb
      simp [arm8ValidImmediate] at hvalid
      cases hb : EncodeBitMask value with
      | none => simp [hb] at hvalid
      | some p => obtain ⟨N, ⟨imms, immr⟩⟩ := p; exact ⟨N, imms, immr, rfl⟩
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC
      (arm8Enc (.inst (.arith (.binop bop destination source (.imm value))))) ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hdom n hn)).symm⟩
  have hast : arm8Ast (.inst (.arith (.binop bop destination source (.imm value)))) =
      [.Data (.«LogicalImmediate@64»
        (1, arm8BopEnc bop, false, value, BitVec.ofNat 5 source, BitVec.ofNat 5 destination))] := by
    rcases hbop with hb | hb <;> subst hb <;> simp [arm8Ast]
  have henc : arm8Enc (.inst (.arith (.binop bop destination source (.imm value)))) =
      arm8Encode (.Data (.«LogicalImmediate@64»
        (1, arm8BopEnc bop, false, value, BitVec.ofNat 5 source, BitVec.ofNat 5 destination))) := by
    rw [arm8Enc, hast]
    simp
  have hlen : (arm8Enc (.inst (.arith (.binop bop destination source (.imm value))))).length = 4 := by
    rw [henc]; exact arm8Encode_length _
  have hop : EncodeLogicalOp (arm8BopEnc bop, false) = some (arm8BopOpcBits bop) := by
    rcases hbop with hb | hb <;> subst hb <;> rfl
  let w : BitVec 32 := arm8LogicalImmediateWord (arm8BopOpcBits bop) N imms immr
    (BitVec.ofNat 5 source) (BitVec.ofNat 5 destination)
  have hword : Encode (.Data (.«LogicalImmediate@64»
      (1, arm8BopEnc bop, false, value, BitVec.ofNat 5 source, BitVec.ofNat 5 destination))) =
      MachineCode.ARM8 w :=
    arm8Encode_logicalImmediate (arm8BopEnc bop) false value _ _ N imms immr
      (arm8BopOpcBits bop) hbm hop
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
  have hdec : Decode w = instruction.Data (Data.«LogicalImmediate@64»
      (1, arm8BopEnc bop, false, value, BitVec.ofNat 5 source,
        BitVec.ofNat 5 destination)) :=
    arm8Decode_logicalImmediate (arm8BopEnc bop) false value _ _ N imms immr
      (arm8BopOpcBits bop) hbm hop
  have hrdne : BitVec.ofNat 5 destination ≠ 31#5 := by
    intro hh
    have hto := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat] at hto
    have h31 : (31#5).toNat = 31 := by decide
    rw [h31] at hto
    have hd32 : destination % 2 ^ 5 = destination := Nat.mod_eq_of_lt (by omega)
    omega
  let v : BitVec 64 := match bop with
    | .and => ms.REG (BitVec.ofNat 5 source) &&& value
    | .or => ms.REG (BitVec.ofNat 5 source) ||| value
    | _ => 0
  have hbr : (Run (instruction.Data (Data.«LogicalImmediate@64»
      (1, arm8BopEnc bop, false, value, BitVec.ofNat 5 source,
        BitVec.ofNat 5 destination))) { ms with branch_hint := none }).branch_hint = none := by
    rw [arm8Run_logicalImmediate _ _ _ _ _ hrdne]
    simp only [«write'X»]
    split <;> rfl
  have hexc : (Run (instruction.Data (Data.«LogicalImmediate@64»
      (1, arm8BopEnc bop, false, value, BitVec.ofNat 5 source,
        BitVec.ofNat 5 destination))) { ms with branch_hint := none }).exception = exception.NoException := by
    rw [arm8Run_logicalImmediate _ _ _ _ _ hrdne]
    simp only [«write'X»]
    split <;> simpa using hexc0
  have hn := arm8Next_word ms w
    (instruction.Data (Data.«LogicalImmediate@64»
      (1, arm8BopEnc bop, false, value, BitVec.ofNat 5 source,
        BitVec.ofNat 5 destination)))
    hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  have hrun : Run (instruction.Data (Data.«LogicalImmediate@64»
      (1, arm8BopEnc bop, false, value, BitVec.ofNat 5 source,
        BitVec.ofNat 5 destination))) { ms with branch_hint := none } =
      { ms with branch_hint := none, REG := holUpdate (BitVec.ofNat 5 destination) v ms.REG } := by
    rw [arm8Run_logicalImmediate _ _ _ _ _ hrdne]
    rw [arm8WriteX_of_valid _ _ hd31 hdlt]
    rcases hbop with hb | hb
    · subst hb
      simp [v, arm8BopEnc, holUpdate, arm8X_of_valid _ hs31 hslt]
    · subst hb
      simp [v, arm8BopEnc, holUpdate, arm8X_of_valid _ hs31 hslt]
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
    rcases hbop with hb | hb
    · subst hb
      simp [asmUpd, instUpd, arithUpd, binopUpd, updReg, updPc, v,
        Flapjack.Compiler.Encoders.AsmSem.readReg, Flapjack.Compiler.Encoders.AsmSem.regImm,
        hreg source ⟨hslt, hsav⟩]
    · subst hb
      simp [asmUpd, instUpd, arithUpd, binopUpd, updReg, updPc, v,
        Flapjack.Compiler.Encoders.AsmSem.readReg, Flapjack.Compiler.Encoders.AsmSem.regImm,
        hreg source ⟨hslt, hsav⟩]
  refine asmCaseOne (.arith (.binop bop destination source (.imm value))) destination v
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
