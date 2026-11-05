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
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_binop_logic_imm (bop : HolBinop)
    (hbop : bop = .and ∨ bop = .or) (destination source : Nat) (value : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.arith (.binop bop destination source (.imm value)))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.arith (.binop bop destination source (.imm value)))) s1 s2 ms := by
  have hs := h.1
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
  have hast : arm8Ast (.inst (.arith (.binop bop destination source (.imm value)))) =
      [.Data (.«LogicalImmediate@64»
        (1, arm8BopEnc bop, false, value, BitVec.ofNat 5 source, BitVec.ofNat 5 destination))] := by
    rcases hbop with hb | hb <;> subst hb <;> simp [arm8Ast]
  have henc : arm8Enc (.inst (.arith (.binop bop destination source (.imm value)))) =
      arm8Encode (.Data (.«LogicalImmediate@64»
        (1, arm8BopEnc bop, false, value, BitVec.ofNat 5 source, BitVec.ofNat 5 destination))) := by
    rw [arm8Enc, hast]
    simp
  have hop : EncodeLogicalOp (arm8BopEnc bop, false) = some (arm8BopOpcBits bop) := by
    rcases hbop with hb | hb <;> subst hb <;> rfl
  let w : BitVec 32 := arm8LogicalImmediateWord (arm8BopOpcBits bop) N imms immr
    (BitVec.ofNat 5 source) (BitVec.ofNat 5 destination)
  have hword : Encode (.Data (.«LogicalImmediate@64»
      (1, arm8BopEnc bop, false, value, BitVec.ofNat 5 source, BitVec.ofNat 5 destination))) =
      MachineCode.ARM8 w :=
    arm8Encode_logicalImmediate (arm8BopEnc bop) false value _ _ N imms immr
      (arm8BopOpcBits bop) hbm hop
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
  refine arm8RegCaseOne _ destination v s1 s2 ms h (by omega) _ _ _ henc hword hdec ?_ ?_
  · intro hreg
    rw [arm8Run_logicalImmediate _ _ _ _ _ hrdne]
    rw [arm8WriteX_of_valid _ _ hd31 hdlt]
    rcases hbop with hb | hb
    · subst hb
      simp [v, arm8BopEnc, holUpdate, arm8X_of_valid _ hs31 hslt]
    · subst hb
      simp [v, arm8BopEnc, holUpdate, arm8X_of_valid _ hs31 hslt]
  · intro hreg p
    refine ⟨?_, fun x => ?_, ?_, fun k => ?_⟩
    · simp [asmUpd, instUpd, arithUpd, updPc]
    · simp [asmUpd, instUpd, arithUpd, binopUpd, updReg, updPc]
    · simp [asmUpd, instUpd, arithUpd, binopUpd, updReg, updPc]
    · rcases hbop with hb | hb
      · subst hb
        simp [asmUpd, instUpd, arithUpd, binopUpd, updReg, updPc, v,
          Flapjack.Compiler.Encoders.AsmSem.readReg, Flapjack.Compiler.Encoders.AsmSem.regImm,
          hreg source ⟨hslt, hsav⟩]
      · subst hb
        simp [asmUpd, instUpd, arithUpd, binopUpd, updReg, updPc, v,
          Flapjack.Compiler.Encoders.AsmSem.readReg, Flapjack.Compiler.Encoders.AsmSem.regImm,
          hreg source ⟨hslt, hsav⟩]

/-- The `binop` `xor` immediate constructor (immediate not `-1`) of
`encoder_correct arm8TargetL3`, lowered to `LogicalImmediate@64` with `EOR`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_binop_xor_imm (destination source : Nat) (value : BitVec 64)
    (hne : value ≠ -1) (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.arith (.binop .xor destination source (.imm value)))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.arith (.binop .xor destination source (.imm value)))) s1 s2 ms := by
  have hs := h.1
  have hokinst : asmOkExact (.inst (.arith (.binop .xor destination source (.imm value))))
      arm8ConfigL3 = true := hs.2.2.2.2.2.2
  have hregok : (asmRegOkExact destination arm8ConfigL3 = true ∧
      asmRegOkExact source arm8ConfigL3 = true) ∧
      asmRegImmOkExact (.inl .xor) (.imm value) arm8ConfigL3 = true := by
    simpa [asmOkExact, asmInstOkExact, asmArithOkExact, arm8ConfigL3,
      Bool.and_eq_true] using hokinst
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hregok.1.1
  obtain ⟨hslt, hsav, hs31⟩ := regOk_of_asmL3 hregok.1.2
  have hvalid : arm8ValidImmediate (.inl .xor) value = true := by
    have hv := hregok.2
    have hbeq : ((Sum.inl BinOp.xor : Sum BinOp Cmp) == (Sum.inl BinOp.xor : Sum BinOp Cmp)) = true := by
      decide
    have hneg : (value == (-1 : BitVec 64)) = false := by
      cases h : (value == (-1 : BitVec 64))
      · rfl
      · exact absurd (by simpa using h) hne
    simpa only [asmRegImmOkExact, arm8ConfigL3, arm8ValidImmediate, hbeq, hneg,
      Bool.true_and, Bool.false_and, Bool.false_or] using hv
  obtain ⟨N, imms, immr, hbm⟩ : ∃ N imms immr, EncodeBitMask value = some (N, (imms, immr)) := by
    simp [arm8ValidImmediate] at hvalid
    cases hb : EncodeBitMask value with
    | none => simp [hb] at hvalid
    | some p => obtain ⟨N, ⟨imms, immr⟩⟩ := p; exact ⟨N, imms, immr, rfl⟩
  have hast : arm8Ast (.inst (.arith (.binop .xor destination source (.imm value)))) =
      [.Data (.«LogicalImmediate@64»
        (1, .LogicalOp_EOR, false, value, BitVec.ofNat 5 source, BitVec.ofNat 5 destination))] := by
    simp only [arm8Ast]
    rw [if_neg hne]
    rfl
  have henc : arm8Enc (.inst (.arith (.binop .xor destination source (.imm value)))) =
      arm8Encode (.Data (.«LogicalImmediate@64»
        (1, .LogicalOp_EOR, false, value, BitVec.ofNat 5 source, BitVec.ofNat 5 destination))) := by
    rw [arm8Enc, hast]
    simp
  have hop : EncodeLogicalOp (.LogicalOp_EOR, false) = some (2 : BitVec 2) := by rfl
  let w : BitVec 32 := arm8LogicalImmediateWord (2 : BitVec 2) N imms immr
    (BitVec.ofNat 5 source) (BitVec.ofNat 5 destination)
  have hword : Encode (.Data (.«LogicalImmediate@64»
      (1, .LogicalOp_EOR, false, value, BitVec.ofNat 5 source, BitVec.ofNat 5 destination))) =
      MachineCode.ARM8 w :=
    arm8Encode_logicalImmediate .LogicalOp_EOR false value _ _ N imms immr
      (2 : BitVec 2) hbm hop
  have hdec : Decode w = instruction.Data (Data.«LogicalImmediate@64»
      (1, .LogicalOp_EOR, false, value, BitVec.ofNat 5 source,
        BitVec.ofNat 5 destination)) :=
    arm8Decode_logicalImmediate .LogicalOp_EOR false value _ _ N imms immr
      (2 : BitVec 2) hbm hop
  have hrdne : BitVec.ofNat 5 destination ≠ 31#5 := by
    intro hh
    have hto := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat] at hto
    have h31 : (31#5).toNat = 31 := by decide
    rw [h31] at hto
    have hd32 : destination % 2 ^ 5 = destination := Nat.mod_eq_of_lt (by omega)
    omega
  let v : BitVec 64 := ms.REG (BitVec.ofNat 5 source) ^^^ value
  refine arm8RegCaseOne _ destination v s1 s2 ms h (by omega) _ _ _ henc hword hdec ?_ ?_
  · intro hreg
    rw [arm8Run_logicalImmediate _ _ _ _ _ hrdne]
    rw [arm8WriteX_of_valid _ _ hd31 hdlt]
    simp [v, holUpdate, arm8X_of_valid _ hs31 hslt]
  · intro hreg p
    refine ⟨?_, fun x => ?_, ?_, fun k => ?_⟩
    · simp [asmUpd, instUpd, arithUpd, updPc]
    · simp [asmUpd, instUpd, arithUpd, binopUpd, updReg, updPc]
    · simp [asmUpd, instUpd, arithUpd, binopUpd, updReg, updPc]
    · simp [asmUpd, instUpd, arithUpd, binopUpd, updReg, updPc, v,
        Flapjack.Compiler.Encoders.AsmSem.readReg, Flapjack.Compiler.Encoders.AsmSem.regImm,
        hreg source ⟨hslt, hsav⟩]

end Flapjack.Compiler.Encoders.Arm8.L3
