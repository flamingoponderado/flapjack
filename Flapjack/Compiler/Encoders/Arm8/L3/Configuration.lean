import Flapjack.Compiler.Encoders.Arm8.L3.Ast
import Flapjack.Compiler.Encoders.Arm8.TargetProof
import Flapjack.Compiler.Encoders.AsmProps.Encoding

/-!
# The L3 ARMv8 assembler configuration

Counterpart of `arm8_config` in
`cakeml/compiler/encoders/arm8/arm8_targetScript.sml`.  Unlike the closed-model
`arm8Config` (`Flapjack/Compiler/Encoders/Arm8/Configuration.lean`), this record
uses the exact L3 carriers: `encode := arm8Enc` over `HolAsm 64`, and
`valid_imm := arm8ValidImmediate` over the rendered L3 `EncodeBitMask`.  It is
the configuration that `arm8TargetL3`, the tagged `arm8_target_def` port in
`L3/Target/State.lean`, instantiates.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Asm

/-- `valid_immediate` (`arm8_targetScript.sml:311-319`): the integer-range test
for `Add`/`Sub`/`Less`/`Lower`/`Equal`/`NotLess`/`NotLower`/`NotEqual`, and the
L3 `EncodeBitMask` check for the bitwise operations. -/
@[hol "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "valid_immediate_def"]
def arm8ValidImmediate (operator : Sum BinOp Cmp) (i : BitVec 64) : Bool :=
  match operator with
  | .inl .add | .inl .sub
  | .inr .less | .inr .lower | .inr .equal
  | .inr .notLess | .inr .notLower | .inr .notEqual =>
      i &&& (~~~(0xFFF : BitVec 64)) = 0 || i &&& (~~~(0xFFF000 : BitVec 64)) = 0
  | _ => (EncodeBitMask i).isSome

/-- `arm8_config` (`arm8_targetScript.sml:321-341`): the exact L3 assembler
configuration. -/
@[hol "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_config_def"]
noncomputable def arm8ConfigL3 : AsmConfigExact 64 where
  isa := .armv8
  encode := arm8Enc
  regCount := 32
  fpRegCount := 0
  avoidRegs := [18, 26, 31]
  linkReg := some 30
  twoRegArith := false
  bigEndian := false
  codeAlignment := 2
  validImm := arm8ValidImmediate
  addrOffset := (-4351, 4350)
  hwOffset := (-4351, 4350)
  byteOffset := (-256, 4095)
  jumpOffset := (-134217728, 134217727)
  cjumpOffset := (-1048572, 1048579)
  locOffset := (-2147483648, 2147483647)

/-- Derived projection of the whole source record; there is no separately
named HOL theorem for this definitional field equality. -/
theorem arm8ConfigL3_encode : arm8ConfigL3.encode = arm8Enc := rfl

/-- `arm8LocInRange` is exactly the signed 20-bit range. -/
theorem arm8LocInRange_iff (a : BitVec 64) :
    arm8LocInRange a = true ↔
      -(2 ^ 19 : Int) ≤ a.toInt ∧ a.toInt ≤ 2 ^ 19 - 1 := by
  unfold arm8LocInRange
  rw [Bool.and_eq_true, BitVec.sle_iff_toInt_le, BitVec.sle_iff_toInt_le]
  have hmin : (BitVec.signExtend 64 (BitVec.ofNat 20 0x80000)).toInt = -(2 ^ 19 : Int) := by
    decide
  have hmax : (BitVec.signExtend 64 (BitVec.ofNat 20 0x7FFFF)).toInt = 2 ^ 19 - 1 := by
    decide
  rw [hmin, hmax]

/-- The `NoOperation` fail list is nonempty. -/
@[simp] theorem arm8EncodeFail_ne : arm8EncodeFail ≠ [] := by simp [arm8EncodeFail]

/-- Every L3 instruction encodes to exactly four bytes. -/
theorem arm8Encode_length (i : instruction) : (arm8Encode i).length = 4 := by
  unfold arm8Encode
  cases h : Encode i <;> simp

/-- `arm8_ast` never returns an empty list. -/
theorem arm8Ast_nonempty (w : HolAsm 64) : arm8Ast w ≠ [] := by
  cases w with
  | inst i =>
      cases i with
      | skip => simp [arm8Ast]
      | const r v =>
          simp only [arm8Ast]
          try (repeat' split)
          all_goals simp
      | arith op =>
          cases op with
          | binop b d s ri =>
              cases ri <;> (simp only [arm8Ast]; try (repeat' split); all_goals simp)
          | shift sh d s ri =>
              cases ri with
              | reg r => simp [arm8Ast]
              | imm v =>
                  cases sh <;> (simp only [arm8Ast]; try (repeat' split); all_goals simp)
          | div d a b => simp [arm8Ast]
          | longMul a b c d => simp [arm8Ast]
          | longDiv a b c d e => simp [arm8Ast]
          | addCarry a b c d => simp [arm8Ast]
          | addOverflow a b c d => simp [arm8Ast]
          | subOverflow a b c d => simp [arm8Ast]
      | mem op d ad =>
          cases ad with
          | addr base off =>
              cases op <;>
                (simp [arm8Ast, arm8LoadStoreAst, arm8LoadStoreAst32, arm8LoadStoreAst16];
                 try (repeat' split); all_goals simp)
      | fp f => simp [arm8Ast]
  | jump t => simp [arm8Ast]
  | jumpCmp op s ri t =>
      cases ri with
      | reg r => simp [arm8Ast]
      | imm v => simp [arm8Ast]
  | call t => simp [arm8Ast]
  | jumpReg r => simp [arm8Ast]
  | loc r off =>
      simp only [arm8Ast]
      try (repeat' split)
      all_goals simp

/-- `arm8_enc` is four bytes per lowered instruction. -/
theorem arm8Enc_length (w : HolAsm 64) :
    (arm8Enc w).length = 4 * (arm8Ast w).length := by
  unfold arm8Enc
  have h : ∀ l : List instruction, (l.flatMap arm8Encode).length = 4 * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
        show (arm8Encode x ++ xs.flatMap arm8Encode).length = 4 * (x :: xs).length
        rw [List.length_append, arm8Encode_length, ih, List.length_cons]
        omega
  exact h (arm8Ast w)

/-- The `loc` length is one instruction inside the signed 20-bit range and six
outside it. -/
theorem arm8Ast_loc_length (register : Nat) (a : BitVec 64) :
    (arm8Ast (.loc register a)).length =
      if arm8LocInRange a then 1 else 6 := by
  simp [arm8Ast, arm8LocInRange]
  split <;> simp

/-- `loc` byte-length monotonicity, nonnegative offsets. -/
theorem arm8Loc_len_pos (register : Nat) (a1 a2 : BitVec 64)
    (h1 : (0 : BitVec 64).sle a1 = true) (h2 : (0 : BitVec 64).sle a2 = true)
    (h12 : a1.sle a2 = true) :
    (arm8Enc (.loc register a1)).length ≤ (arm8Enc (.loc register a2)).length := by
  rw [arm8Enc_length, arm8Enc_length, arm8Ast_loc_length, arm8Ast_loc_length]
  rw [BitVec.sle_iff_toInt_le] at h1 h2 h12
  have hz : (0 : BitVec 64).toInt = 0 := rfl
  rw [hz] at h1 h2
  by_cases hf1 : arm8LocInRange a1 = true
  · by_cases hf2 : arm8LocInRange a2 = true
    · simp [hf1, hf2]
    · simp [hf1, hf2]
  · by_cases hf2 : arm8LocInRange a2 = true
    · simp [hf1, hf2]
      have n1 := (arm8LocInRange_iff a1).not.1 hf1
      have b2 := (arm8LocInRange_iff a2).1 hf2
      omega
    · simp [hf1, hf2]

/-- `loc` byte-length monotonicity, negative offsets. -/
theorem arm8Loc_len_neg (register : Nat) (a1 a2 : BitVec 64)
    (h1 : a1.slt 0 = true) (h2 : a2.slt 0 = true)
    (h21 : a2.sle a1 = true) :
    (arm8Enc (.loc register a1)).length ≤ (arm8Enc (.loc register a2)).length := by
  rw [arm8Enc_length, arm8Enc_length, arm8Ast_loc_length, arm8Ast_loc_length]
  rw [BitVec.slt_iff_toInt_lt] at h1 h2
  rw [BitVec.sle_iff_toInt_le] at h21
  have hz : (0 : BitVec 64).toInt = 0 := rfl
  rw [hz] at h1 h2
  by_cases hf1 : arm8LocInRange a1 = true
  · by_cases hf2 : arm8LocInRange a2 = true
    · simp [hf1, hf2]
    · simp [hf1, hf2]
  · by_cases hf2 : arm8LocInRange a2 = true
    · simp [hf1, hf2]
      have n1 := (arm8LocInRange_iff a1).not.1 hf1
      have b1 := (arm8LocInRange_iff a2).1 hf2
      omega
    · simp [hf1, hf2]

/-- `enc_ok` for the exact L3 ARMv8 configuration. -/
theorem arm8ConfigL3_encOk : encOk arm8ConfigL3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [arm8ConfigL3, arm8Enc_length, arm8Ast]
  · intro instruction
    constructor
    · simp [arm8ConfigL3, arm8Enc_length]
    · simp only [arm8ConfigL3, arm8Enc_length]
      have hn := List.length_pos_iff.mpr (arm8Ast_nonempty instruction)
      omega
  · intro w1 w2 _
    simp [arm8ConfigL3, arm8Enc_length, arm8Ast]
  · intro cmp reg ri w1 w2 _
    cases ri <;> simp [arm8ConfigL3, arm8Enc_length, arm8Ast]
  · intro w1 w2 _
    simp [arm8ConfigL3, arm8Enc_length, arm8Ast]
  · intro w1 w2 reg _
    constructor
    · intro h
      rcases h with ⟨h1, h2, h12⟩
      exact arm8Loc_len_pos reg w1 w2 h1 h2 h12
    · intro h
      rcases h with ⟨h1, h2, h21⟩
      exact arm8Loc_len_neg reg w1 w2 h1 h2 h21

end Flapjack.Compiler.Encoders.Arm8.L3
