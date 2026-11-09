module

public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.MoveWide
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.LogicalImmediate
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Const

@[expose] public section

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

/-- The four encoded bytes of `AddSubShiftedRegister@64`. -/
theorem arm8EncodeBytes_addSubShiftedRegister (op s : Bool) (shift : ShiftType)
    (rm : BitVec 5) (amount : BitVec 6) (rn rd : BitVec 5) :
    arm8Encode (.Data (.«AddSubShiftedRegister@64»
      ((1 : BitVec 64), (op, (s, (shift, (rm, (amount, (rn, rd))))))))) =
      [BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord op s shift rm amount rn rd >>> 0).toNat),
       BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord op s shift rm amount rn rd >>> 8).toNat),
       BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord op s shift rm amount rn rd >>> 16).toNat),
       BitVec.ofNat 8 ((arm8AddSubShiftedRegisterWord op s shift rm amount rn rd >>> 24).toNat)] := by
  rw [arm8Encode, arm8Encode_addSubShiftedRegister]

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
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_binop_addsub_reg (op : Bool) (bop : HolBinop)
    (hbop : bop = if op then .sub else .add) (destination source right : Nat)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.arith (.binop bop destination source (.reg right)))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.arith (.binop bop destination source (.reg right)))) s1 s2 ms := by
  have hs := h.1
  have hregok : (asmRegOkExact destination arm8ConfigL3 = true ∧
      asmRegOkExact source arm8ConfigL3 = true) ∧
      asmRegOkExact right arm8ConfigL3 = true := by
    have hk := hs.2.2.2.2.2.2
    simpa [asmOkExact, asmInstOkExact, asmArithOkExact, asmRegImmOkExact, arm8ConfigL3,
      Bool.and_eq_true] using hk
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hregok.1.1
  obtain ⟨hslt, hsav, hs31⟩ := regOk_of_asmL3 hregok.1.2
  obtain ⟨hrlt, hrav, hr31⟩ := regOk_of_asmL3 hregok.2
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
  let w : BitVec 32 := arm8AddSubShiftedRegisterWord op false .lsl
    (BitVec.ofNat 5 right) 0 (BitVec.ofNat 5 source) (BitVec.ofNat 5 destination)
  have hdec : Decode w = instruction.Data (Data.«AddSubShiftedRegister@64»
      ((1 : BitVec 64), (op, (false, (ShiftType.lsl, (BitVec.ofNat 5 right,
        (0, (BitVec.ofNat 5 source, BitVec.ofNat 5 destination)))))))) :=
    arm8Decode_addSubShiftedRegister op false _ _ _ _
  let v : BitVec 64 := if op then
      ms.REG (BitVec.ofNat 5 source) - ms.REG (BitVec.ofNat 5 right)
    else ms.REG (BitVec.ofNat 5 source) + ms.REG (BitVec.ofNat 5 right)
  refine arm8RegCaseOne _ destination v s1 s2 ms h (by omega) _ _ _ henc (by rw [arm8Encode_addSubShiftedRegister]) hdec ?_ ?_
  · intro hreg
    rw [arm8Run_addSubShiftedRegister]
    cases op
    · simp only [SetTheFlags, Bool.false_eq_true, if_false, ShiftReg, ShiftValue]
      rw [arm8WriteX_of_valid _ _ hd31 hdlt, arm8X_of_valid _ hs31 hslt, arm8X_of_valid _ hr31 hrlt]
      simp [arm8AddWithCarry_add, holUpdate, v]
    · simp only [SetTheFlags, Bool.false_eq_true, if_false, ShiftReg, ShiftValue]
      rw [arm8WriteX_of_valid _ _ hd31 hdlt, arm8X_of_valid _ hs31 hslt, arm8X_of_valid _ hr31 hrlt]
      simp [arm8AddWithCarry_sub, holUpdate, v]
  · intro hreg p
    refine ⟨?_, fun x => ?_, ?_, fun k => ?_⟩
    · simp [asmUpd, instUpd, arithUpd, updPc]
    · simp [asmUpd, instUpd, arithUpd, binopUpd, updReg, updPc]
    · simp [asmUpd, instUpd, arithUpd, binopUpd, updReg, updPc]
    · cases op
      · simp [asmUpd, instUpd, arithUpd, binopUpd, updReg, updPc, hbop, v,
          Flapjack.Compiler.Encoders.AsmSem.readReg, Flapjack.Compiler.Encoders.AsmSem.regImm,
          hreg source ⟨hslt, hsav⟩, hreg right ⟨hrlt, hrav⟩]
      · simp [asmUpd, instUpd, arithUpd, binopUpd, updReg, updPc, hbop, v,
          Flapjack.Compiler.Encoders.AsmSem.readReg, Flapjack.Compiler.Encoders.AsmSem.regImm,
          hreg source ⟨hslt, hsav⟩, hreg right ⟨hrlt, hrav⟩]

end Flapjack.Compiler.Encoders.Arm8.L3


