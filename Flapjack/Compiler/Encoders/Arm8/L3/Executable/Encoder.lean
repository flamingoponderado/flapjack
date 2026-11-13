module

public import Flapjack.Compiler.Encoders.Arm8.L3.Executable.Defs
public import Flapjack.Compiler.Encoders.Arm8.L3.Executable.Guards
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.MoveWide
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Arith
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Shift
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Division
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Multiply
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.ConditionalSelect
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Carry
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.ShiftImmediate
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.JumpReg

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-!
# The computable encoder's bytes for the unguarded instruction forms

For each `Insn` form that `Arm8.arm8Ast` emits without an immediate-range
guard, `encodeBytes` is exactly `L3.arm8Encode` of the corresponding L3
`instruction`.  Each case proves that `fields` builds the reviewed
`arm8Encode_*` word of `L3/CorrectnessEncoding/`, then reuses that theorem.

No new HOL claim is introduced: the bridge relates two Lean renderings of the
same instruction word.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem

/-- `Arm8.shiftTypeBits` is the rendered `ShiftType2num`. -/
theorem shiftTypeBits_eq (sh : ShiftType) : shiftTypeBits sh = ShiftType2num sh := by
  cases sh <;> rfl

/-- The `MoveWide` word: `fields` and the L3 concatenation agree. -/
theorem fields_moveWide (op : MoveWideOp) (hw imm16 rd : Nat) :
    fields [(1, 1), (2, moveWideOpBits op), (6, 0b100101), (2, hw), (16, imm16), (5, rd)]
      = arm8MoveWideWord op (BitVec.ofNat 2 hw) (BitVec.ofNat 16 imm16) (BitVec.ofNat 5 rd) := by
  cases op <;>
    · simp only [fields, List.foldl_cons, List.foldl_nil, arm8MoveWideWord, moveWideOpBits]
      rw [ofNat_mod_setWidth 1, ofNat_mod_setWidth 2, ofNat_mod_setWidth 6, ofNat_mod_setWidth 16, ofNat_mod_setWidth 5]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
        BitVec.getLsbD_append, BitVec.getLsbD_setWidth, Nat.testBit_mod_two_pow]
      interval_cases i <;> simp

/-- The `AddSubShiftedRegister@64` word. -/
theorem fields_addSubShiftedRegister (sub setFlags : Bool) (shift : ShiftType)
    (rm imm6 rn rd : Nat) :
    fields [(1, 1), (1, bit sub), (1, bit setFlags), (5, 0b01011),
      (2, shiftTypeBits shift), (1, 0), (5, rm), (6, imm6), (5, rn), (5, rd)]
      = arm8AddSubShiftedRegisterWord sub setFlags shift (BitVec.ofNat 5 rm)
          (BitVec.ofNat 6 imm6) (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd) := by
  cases sub <;> cases setFlags <;> cases shift <;>
    · simp only [fields, List.foldl_cons, List.foldl_nil, arm8AddSubShiftedRegisterWord,
        shiftTypeBits, ShiftType2num, bit_false, bit_true, holV2w_one_true, holV2w_one_false]
      rw [ofNat_mod_setWidth 1, ofNat_mod_setWidth 5, ofNat_mod_setWidth 2, ofNat_mod_setWidth 6]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
        BitVec.getLsbD_append, BitVec.getLsbD_setWidth, Nat.testBit_mod_two_pow]
      interval_cases i <;> simp
      all_goals decide

/-- The `Shift@64` word. -/
theorem fields_shift (sh : ShiftType) (rm rn rd : Nat) :
    fields [(11, 1238), (5, rm), (4, 2), (2, shiftTypeBits sh), (5, rn), (5, rd)]
      = arm8ShiftWord sh (BitVec.ofNat 5 rm) (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd) := by
  cases sh <;>
    · simp only [fields, List.foldl_cons, List.foldl_nil, arm8ShiftWord, shiftTypeBits,
        ShiftType2num]
      rw [ofNat_mod_setWidth 11, ofNat_mod_setWidth 5, ofNat_mod_setWidth 4, ofNat_mod_setWidth 2]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
        BitVec.getLsbD_append, BitVec.getLsbD_setWidth, Nat.testBit_mod_two_pow]
      interval_cases i <;> simp
      all_goals decide

/-- The `Division@64` word. -/
theorem fields_division (o1 : Bool) (rm rn rd : Nat) :
    fields [(11, 1238), (5, rm), (5, 1), (1, bit (!o1)), (5, rn), (5, rd)]
      = arm8DivisionWord o1 (BitVec.ofNat 5 rm) (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd) := by
  cases o1 <;>
    · simp only [fields, List.foldl_cons, List.foldl_nil, arm8DivisionWord,
        bit_false, bit_true, Bool.not_false, Bool.not_true,
        holV2w_one_true, holV2w_one_false]
      rw [ofNat_mod_setWidth 11, ofNat_mod_setWidth 5, ofNat_mod_setWidth 1]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
        BitVec.getLsbD_append, BitVec.getLsbD_setWidth, Nat.testBit_mod_two_pow]
      interval_cases i <;> simp

/-- The `MultiplyHigh` word. -/
theorem fields_multiplyHigh (u : Bool) (rm rn rd : Nat) :
    fields [(8, 155), (1, bit (!u)), (2, 2), (5, rm), (6, 31), (5, rn), (5, rd)]
      = arm8MultiplyHighWord u (BitVec.ofNat 5 rm) (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd) := by
  cases u <;>
    · simp only [fields, List.foldl_cons, List.foldl_nil, arm8MultiplyHighWord,
        bit_false, bit_true, Bool.not_false, Bool.not_true,
        holV2w_one_true, holV2w_one_false]
      rw [ofNat_mod_setWidth 8, ofNat_mod_setWidth 1, ofNat_mod_setWidth 2, ofNat_mod_setWidth 5, ofNat_mod_setWidth 6]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
        BitVec.getLsbD_append, BitVec.getLsbD_setWidth, Nat.testBit_mod_two_pow]
      interval_cases i <;> simp

/-- The `MultiplyAddSub@64` word. -/
theorem fields_multiplyAddSub (o0 : Bool) (rm ra rn rd : Nat) :
    fields [(11, 1240), (5, rm), (1, bit o0), (5, ra), (5, rn), (5, rd)]
      = arm8MultiplyAddSubWord o0 (BitVec.ofNat 5 rm) (BitVec.ofNat 5 ra)
          (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd) := by
  cases o0 <;>
    · simp only [fields, List.foldl_cons, List.foldl_nil, arm8MultiplyAddSubWord,
        bit_false, bit_true, holV2w_one_true, holV2w_one_false]
      rw [ofNat_mod_setWidth 11, ofNat_mod_setWidth 5, ofNat_mod_setWidth 1]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
        BitVec.getLsbD_append, BitVec.getLsbD_setWidth, Nat.testBit_mod_two_pow]
      interval_cases i <;> simp

/-- The `ConditionalSelect@64` word. -/
theorem fields_conditionalSelect (op o2 : Bool) (cd rm rn rd : Nat) :
    fields [(1, 1), (1, bit op), (9, 212), (5, rm), (4, cd), (1, 0), (1, bit o2),
      (5, rn), (5, rd)]
      = arm8ConditionalSelectWord op o2 (BitVec.ofNat 4 cd) (BitVec.ofNat 5 rm)
          (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd) := by
  cases op <;> cases o2 <;>
    · simp only [fields, List.foldl_cons, List.foldl_nil, arm8ConditionalSelectWord,
        bit_false, bit_true, holV2w_one_true, holV2w_one_false]
      rw [ofNat_mod_setWidth 1, ofNat_mod_setWidth 9, ofNat_mod_setWidth 5, ofNat_mod_setWidth 4]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
        BitVec.getLsbD_append, BitVec.getLsbD_setWidth, Nat.testBit_mod_two_pow]
      interval_cases i <;> simp

/-- The `AddSubCarry@64` word. -/
theorem fields_addSubCarry (sub setFlags : Bool) (rm rn rd : Nat) :
    fields [(1, 1), (1, bit sub), (1, bit setFlags), (8, 208), (5, rm), (6, 0),
      (5, rn), (5, rd)]
      = arm8AddSubCarryWord sub setFlags (BitVec.ofNat 5 rm)
          (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd) := by
  cases sub <;> cases setFlags <;>
    · simp only [fields, List.foldl_cons, List.foldl_nil, arm8AddSubCarryWord,
        bit_false, bit_true, holV2w_one_true, holV2w_one_false]
      rw [ofNat_mod_setWidth 1, ofNat_mod_setWidth 8, ofNat_mod_setWidth 5, ofNat_mod_setWidth 6]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
        BitVec.getLsbD_append, BitVec.getLsbD_setWidth, Nat.testBit_mod_two_pow]
      interval_cases i <;> simp

/-- The `ExtractRegister@64` word. -/
theorem fields_extractRegister (imms rm rn rd : Nat) :
    fields [(11, 1182), (5, rm), (6, imms), (5, rn), (5, rd)]
      = arm8ExtractWord (BitVec.ofNat 6 imms) (BitVec.ofNat 5 rm)
          (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd) := by
  simp only [fields, List.foldl_cons, List.foldl_nil, arm8ExtractWord]
  rw [ofNat_mod_setWidth 11, ofNat_mod_setWidth 5, ofNat_mod_setWidth 6]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
    BitVec.getLsbD_append, BitVec.getLsbD_setWidth, Nat.testBit_mod_two_pow]
  interval_cases i <;> simp

/-- The `BranchRegister` word. -/
theorem fields_branchRegister (rn : Nat) :
    fields [(9, 428), (2, 0), (11, 1984), (5, rn), (5, 0)]
      = arm8JumpRegWord (BitVec.ofNat 5 rn) := by
  simp only [fields, List.foldl_cons, List.foldl_nil, arm8JumpRegWord]
  rw [ofNat_mod_setWidth 9, ofNat_mod_setWidth 2, ofNat_mod_setWidth 11, ofNat_mod_setWidth 5]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
    BitVec.getLsbD_append, BitVec.getLsbD_setWidth, Nat.testBit_mod_two_pow]
  interval_cases i <;> simp

/-- `NoOperation` encodes to the same four bytes on both sides. -/
theorem encodeBytes_noOp : encodeBytes .noOp = arm8Encode NoOperation := by
  rw [arm8Encode_nop]
  decide

/-- A `MoveWide` instruction encodes to the same four bytes. -/
theorem encodeBytes_moveWide (op : MoveWideOp) (hw imm16 rd : Nat) :
    encodeBytes (.moveWide op hw imm16 rd) =
      arm8Encode (.Data (.«MoveWide@64»
        ((1 : BitVec 64), (op, (BitVec.ofNat 2 hw, (BitVec.ofNat 16 imm16, BitVec.ofNat 5 rd)))))) := by
  have hw' : encodeInsn32 (.moveWide op hw imm16 rd) =
      some (arm8MoveWideWord op (BitVec.ofNat 2 hw) (BitVec.ofNat 16 imm16) (BitVec.ofNat 5 rd)) := by
    simp only [encodeInsn32]
    rw [fields_moveWide]
  rw [encodeBytes_eq_of_encodeInsn32 _ _ hw', arm8Encode, arm8Encode_moveWide]

/-- An `AddSubShiftedRegister` encodes to the same four bytes. -/
theorem encodeBytes_addSubShiftedRegister (sub setFlags : Bool) (shift : ShiftType)
    (rm imm6 rn rd : Nat) :
    encodeBytes (.addSubShiftedRegister sub setFlags shift rm imm6 rn rd) =
      arm8Encode (.Data (.«AddSubShiftedRegister@64»
        ((1 : BitVec 64), (sub, (setFlags, (shift,
          (BitVec.ofNat 5 rm, (BitVec.ofNat 6 imm6, (BitVec.ofNat 5 rn, BitVec.ofNat 5 rd))))))))) := by
  have hw' : encodeInsn32 (.addSubShiftedRegister sub setFlags shift rm imm6 rn rd) =
      some (arm8AddSubShiftedRegisterWord sub setFlags shift
        (BitVec.ofNat 5 rm) (BitVec.ofNat 6 imm6) (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd)) := by
    simp only [encodeInsn32]
    rw [fields_addSubShiftedRegister]
  rw [encodeBytes_eq_of_encodeInsn32 _ _ hw', arm8Encode, arm8Encode_addSubShiftedRegister]

/-- A `Shift@64` encodes to the same four bytes. -/
theorem encodeBytes_shift (sh : ShiftType) (rm rn rd : Nat) :
    encodeBytes (.shift sh rm rn rd) =
      arm8Encode (.Data (.«Shift@64»
        ((1 : BitVec 64), (sh, (BitVec.ofNat 5 rm, (BitVec.ofNat 5 rn, BitVec.ofNat 5 rd)))))) := by
  have hw' : encodeInsn32 (.shift sh rm rn rd) =
      some (arm8ShiftWord sh (BitVec.ofNat 5 rm) (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd)) := by
    simp only [encodeInsn32]
    rw [fields_shift]
  rw [encodeBytes_eq_of_encodeInsn32 _ _ hw', arm8Encode, arm8Encode_shift]

/-- A `Division@64` encodes to the same four bytes. -/
theorem encodeBytes_division (o1 : Bool) (rm rn rd : Nat) :
    encodeBytes (.division o1 rm rn rd) =
      arm8Encode (.Data (.«Division@64»
        ((1 : BitVec 64), (o1, (BitVec.ofNat 5 rm, (BitVec.ofNat 5 rn, BitVec.ofNat 5 rd)))))) := by
  have hw' : encodeInsn32 (.division o1 rm rn rd) =
      some (arm8DivisionWord o1 (BitVec.ofNat 5 rm) (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd)) := by
    simp only [encodeInsn32]
    rw [fields_division]
  rw [encodeBytes_eq_of_encodeInsn32 _ _ hw', arm8Encode, arm8Encode_division]

/-- A `MultiplyHigh` encodes to the same four bytes. -/
theorem encodeBytes_multiplyHigh (u : Bool) (rm rn rd : Nat) :
    encodeBytes (.multiplyHigh u rm rn rd) =
      arm8Encode (.Data (.MultiplyHigh
        (u, (BitVec.ofNat 5 rm, (BitVec.ofNat 5 rn, BitVec.ofNat 5 rd))))) := by
  have hw' : encodeInsn32 (.multiplyHigh u rm rn rd) =
      some (arm8MultiplyHighWord u (BitVec.ofNat 5 rm) (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd)) := by
    simp only [encodeInsn32]
    rw [fields_multiplyHigh]
  rw [encodeBytes_eq_of_encodeInsn32 _ _ hw', arm8Encode, arm8Encode_multiplyHigh]

/-- A `MultiplyAddSub@64` encodes to the same four bytes. -/
theorem encodeBytes_multiplyAddSub (o0 : Bool) (rm ra rn rd : Nat) :
    encodeBytes (.multiplyAddSub o0 rm ra rn rd) =
      arm8Encode (.Data (.«MultiplyAddSub@64»
        ((1 : BitVec 64), (o0,
          (BitVec.ofNat 5 rm, (BitVec.ofNat 5 ra, (BitVec.ofNat 5 rn, BitVec.ofNat 5 rd))))))) := by
  have hw' : encodeInsn32 (.multiplyAddSub o0 rm ra rn rd) =
      some (arm8MultiplyAddSubWord o0 (BitVec.ofNat 5 rm) (BitVec.ofNat 5 ra)
        (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd)) := by
    simp only [encodeInsn32]
    rw [fields_multiplyAddSub]
  rw [encodeBytes_eq_of_encodeInsn32 _ _ hw', arm8Encode, arm8Encode_multiplyAddSub]

/-- A `ConditionalSelect@64` encodes to the same four bytes. -/
theorem encodeBytes_conditionalSelect (op o2 : Bool) (cd rm rn rd : Nat) :
    encodeBytes (.conditionalSelect op o2 cd rm rn rd) =
      arm8Encode (.Data (.«ConditionalSelect@64»
        ((1 : BitVec 64), (op, (o2, (BitVec.ofNat 4 cd,
          (BitVec.ofNat 5 rm, (BitVec.ofNat 5 rn, BitVec.ofNat 5 rd)))))))) := by
  have hw' : encodeInsn32 (.conditionalSelect op o2 cd rm rn rd) =
      some (arm8ConditionalSelectWord op o2 (BitVec.ofNat 4 cd)
        (BitVec.ofNat 5 rm) (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd)) := by
    simp only [encodeInsn32]
    rw [fields_conditionalSelect]
  rw [encodeBytes_eq_of_encodeInsn32 _ _ hw', arm8Encode, arm8Encode_conditionalSelect]

/-- An `AddSubCarry@64` encodes to the same four bytes. -/
theorem encodeBytes_addSubCarry (sub setFlags : Bool) (rm rn rd : Nat) :
    encodeBytes (.addSubCarry sub setFlags rm rn rd) =
      arm8Encode (.Data (.«AddSubCarry@64»
        ((1 : BitVec 64), (sub, (setFlags,
          (BitVec.ofNat 5 rm, (BitVec.ofNat 5 rn, BitVec.ofNat 5 rd))))))) := by
  have hw' : encodeInsn32 (.addSubCarry sub setFlags rm rn rd) =
      some (arm8AddSubCarryWord sub setFlags (BitVec.ofNat 5 rm)
        (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd)) := by
    simp only [encodeInsn32]
    rw [fields_addSubCarry]
  rw [encodeBytes_eq_of_encodeInsn32 _ _ hw', arm8Encode, arm8Encode_addSubCarry]

/-- An `ExtractRegister@64` encodes to the same four bytes. -/
theorem encodeBytes_extractRegister (imms rm rn rd : Nat) :
    encodeBytes (.extractRegister imms rm rn rd) =
      arm8Encode (.Data (.«ExtractRegister@64»
        ((1 : BitVec 64), (BitVec.ofNat 6 imms,
          (BitVec.ofNat 5 rm, (BitVec.ofNat 5 rn, BitVec.ofNat 5 rd)))))) := by
  have hw' : encodeInsn32 (.extractRegister imms rm rn rd) =
      some (arm8ExtractWord (BitVec.ofNat 6 imms) (BitVec.ofNat 5 rm)
        (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd)) := by
    simp only [encodeInsn32]
    rw [fields_extractRegister]
  rw [encodeBytes_eq_of_encodeInsn32 _ _ hw', arm8Encode, arm8Encode_extract]

/-- A `JMP`-typed branch register encodes to the same four bytes. -/
theorem encodeBytes_branchRegister (rn : Nat) :
    encodeBytes (.branchRegister rn .jmp) =
      arm8Encode (.Branch (.BranchRegister (BitVec.ofNat 5 rn, .BranchType_JMP))) := by
  have hw' : encodeInsn32 (.branchRegister rn .jmp) =
      some (arm8JumpRegWord (BitVec.ofNat 5 rn)) := by
    simp only [encodeInsn32]
    rw [fields_branchRegister]
  rw [encodeBytes_eq_of_encodeInsn32 _ _ hw', arm8Encode, arm8Encode_branchRegister]

/-- The computable `encMovImm` is the L3 `arm8EncMovImm` on the `BitVec` carrier,
including the failure case. -/
theorem encMovImm_eq (i : BitVec 64) :
    (encMovImm i).map (fun p => (BitVec.ofNat 16 p.1, BitVec.ofNat 2 p.2)) =
      arm8EncMovImm i := by
  have hm1 : (~~~(0xFFFF : BitVec 64)) = (0xFFFFFFFFFFFF0000 : BitVec 64) := by decide
  have hm2 : (~~~(0xFFFF0000 : BitVec 64)) = (0xFFFFFFFF0000FFFF : BitVec 64) := by decide
  have hm3 : (~~~(0xFFFF00000000 : BitVec 64)) = (0xFFFF0000FFFFFFFF : BitVec 64) := by decide
  have hm4 : (~~~(0xFFFF000000000000 : BitVec 64)) = (0x0000FFFFFFFFFFFF : BitVec 64) := by decide
  have h16 : ∀ n : Nat, BitVec.ofNat 16 (n % 65536) = BitVec.ofNat 16 n := by
    intro n
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
  have hi : i >>> (0 : Nat) = i := by simp
  unfold encMovImm arm8EncMovImm
  rw [hm1, hm2, hm3, hm4]
  by_cases h1 : i &&& (0xFFFFFFFFFFFF0000 : BitVec 64) = 0
  · simp only [ite_eq_left h1, Option.map_some]
    simp
    rw [h16]
    rfl
  · by_cases h2 : i &&& (0xFFFFFFFF0000FFFF : BitVec 64) = 0
    · simp only [ite_eq_right h1, ite_eq_left h2, Option.map_some]
      simp
      rw [h16]
    · by_cases h3 : i &&& (0xFFFF0000FFFFFFFF : BitVec 64) = 0
      · simp only [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3, Option.map_some]
        simp
        rw [h16]
      · by_cases h4 : i &&& (0x0000FFFFFFFFFFFF : BitVec 64) = 0
        · simp only [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left h4, Option.map_some]
          simp
          rw [h16]
        · simp only [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
          rfl

end Flapjack.Compiler.Encoders.Arm8.L3
