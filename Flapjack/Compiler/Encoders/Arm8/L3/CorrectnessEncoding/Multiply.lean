import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.LogicalShiftedRegister

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

/-!
# `MultiplyHigh` and `MultiplyAddSub@64`: the `longMul` lowering

`arm8_ast` lowers `Arith (LongMul high low left right)` to two instructions:
`MultiplyHigh (false, right, left, high)` followed by
`MultiplyAddSub@64 (1, false, right, 31, left, low)`.  The first writes the top
64 bits of the unsigned 128-bit product of the two sources; the second writes
the low 64 bits (`left * right + ZR`), matching the `longMul` update
`(r / 2 ^ 64, r % 2 ^ 64)` with `r = left.toNat * right.toNat`.

This module records the words, the `Encode`/`Decode` inverses, the `Run`
semantics and the high-half arithmetic identity.  The case theorem of
`encoder_correct arm8TargetL3` is not built here.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The word emitted for `MultiplyHigh`: HOL's `e_data` term
`0b10011011 ++ (!u) ++ 10 ++ Rm ++ 011111 ++ Rn ++ Rd` (Flapjack
infrastructure: a readable abbreviation for a mechanically rendered term). -/
def arm8MultiplyHighWord (u : Bool) (rm rn rd : BitVec 5) : BitVec 32 :=
  BitVec.setWidth 32 ((BitVec.ofNat 8 155) ++
    BitVec.setWidth 24 (holV2w 1 [!u] ++
      BitVec.setWidth 23 ((BitVec.ofNat 2 2) ++
        BitVec.setWidth 21 (rm ++
          BitVec.setWidth 16 ((BitVec.ofNat 6 31) ++
            BitVec.setWidth 10 (rn ++ rd))))))

/-- `e_data` of `MultiplyHigh` is the multiply-high word (Flapjack
infrastructure; no separately named HOL declaration). -/
theorem arm8EData_multiplyHigh (u : Bool) (rm rn rd : BitVec 5) :
    e_data (.MultiplyHigh (u, (rm, (rn, rd)))) =
      MachineCode.ARM8 (arm8MultiplyHighWord u rm rn rd) := by
  rfl

/-- `Encode` of `MultiplyHigh` is the multiply-high word (Flapjack
infrastructure; no separately named HOL declaration). -/
theorem arm8Encode_multiplyHigh (u : Bool) (rm rn rd : BitVec 5) :
    Encode (.Data (.MultiplyHigh (u, (rm, (rn, rd))))) =
      MachineCode.ARM8 (arm8MultiplyHighWord u rm rn rd) := by
  simp only [Encode, arm8EData_multiplyHigh]

/-- The rendered `Decode` inverts `arm8MultiplyHighWord` for the unsigned form
used by `arm8_ast`. -/
theorem arm8Decode_multiplyHigh (rm rn rd : BitVec 5) :
    Decode (arm8MultiplyHighWord false rm rn rd) =
      instruction.Data (Data.MultiplyHigh (false, (rm, (rn, rd)))) := by
  simp only [arm8MultiplyHighWord, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  simp [holV2w_one_true, holV2w_five]

/-- `Run` of `MultiplyHigh`: write the top 64 bits of the extended product of
`Rn` and `Rm` to `Rd`. -/
theorem arm8Run_multiplyHigh (u : Bool) (rm rn rd : BitVec 5) (st : arm8_state) :
    Run (instruction.Data (Data.MultiplyHigh (u, (rm, (rn, rd))))) st =
      «write'X» (holWordExtract 64 127 64
        (ExtendWord (TM := 64) (TN := 128) (X (TN := 64) rn st, u) *
          ExtendWord (TM := 64) (TN := 128) (X (TN := 64) rm st, u)), rd) st := by
  simp only [Run, «dfn'MultiplyHigh»]

/-- The high half of the unsigned 128-bit product is `r / 2 ^ 64` with
`r = a.toNat * b.toNat`. -/
theorem arm8MultiplyHigh_high (a b : BitVec 64) :
    holWordExtract 64 127 64
      (ExtendWord (TM := 64) (TN := 128) (a, false) *
        ExtendWord (TM := 64) (TN := 128) (b, false)) =
      BitVec.ofNat 64 ((a.toNat * b.toNat) / 2 ^ 64) := by
  have ha : (BitVec.setWidth 128 a).toNat = a.toNat := by
    rw [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (by have := a.isLt; omega)
  have hb : (BitVec.setWidth 128 b).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (by have := b.isLt; omega)
  have hlt : a.toNat * b.toNat < 2 ^ 128 := by
    have ha' := a.isLt
    have hb' := b.isLt
    calc a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha' hb'
      _ = 2 ^ 128 := by norm_num
  have hprod : (BitVec.setWidth 128 a * BitVec.setWidth 128 b).toNat
      = a.toNat * b.toNat % 2 ^ 128 := by
    rw [BitVec.toNat_mul, ha, hb]
  have hexp : min 127 (128 - 1) + 1 - 64 = 64 := by norm_num
  simp only [ExtendWord, Bool.false_eq_true, if_false]
  simp only [Flapjack.RiscV.L3.holWordExtract, hprod, hexp]
  rw [Nat.mod_eq_of_lt hlt, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega)]
  have hN' : (a.toNat * b.toNat) / 2 ^ 64 < 2 ^ 128 := by omega
  rw [BitVec.setWidth, dif_neg (by norm_num : ¬ 128 ≤ 64), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hN']

/-- The word emitted for `MultiplyAddSub@64`: HOL's `e_data` term
`0b10011011000 ++ Rm ++ o0 ++ Ra ++ Rn ++ Rd` (Flapjack infrastructure: a
readable abbreviation for a mechanically rendered term). -/
def arm8MultiplyAddSubWord (o0 : Bool) (rm ra rn rd : BitVec 5) : BitVec 32 :=
  BitVec.setWidth 32 ((BitVec.ofNat 11 1240) ++
    BitVec.setWidth 21 (rm ++
      BitVec.setWidth 16 (holV2w 1 [o0] ++
        BitVec.setWidth 15 (ra ++
          BitVec.setWidth 10 (rn ++ rd)))))

/-- `e_data` of `MultiplyAddSub@64` is the multiply-add-sub word (Flapjack
infrastructure; no separately named HOL declaration). -/
theorem arm8EData_multiplyAddSub (o0 : Bool) (rm ra rn rd : BitVec 5) :
    e_data (.«MultiplyAddSub@64» ((1 : BitVec 64), (o0, (rm, (ra, (rn, rd)))))) =
      MachineCode.ARM8 (arm8MultiplyAddSubWord o0 rm ra rn rd) := by
  rfl

/-- `Encode` of `MultiplyAddSub@64` is the multiply-add-sub word (Flapjack
infrastructure; no separately named HOL declaration). -/
theorem arm8Encode_multiplyAddSub (o0 : Bool) (rm ra rn rd : BitVec 5) :
    Encode (.Data (.«MultiplyAddSub@64» ((1 : BitVec 64), (o0, (rm, (ra, (rn, rd))))))) =
      MachineCode.ARM8 (arm8MultiplyAddSubWord o0 rm ra rn rd) := by
  simp only [Encode, arm8EData_multiplyAddSub]

/-- The rendered `Decode` inverts `arm8MultiplyAddSubWord` for the add form used
by `arm8_ast`. -/
theorem arm8Decode_multiplyAddSub (rm ra rn rd : BitVec 5) :
    Decode (arm8MultiplyAddSubWord false rm ra rn rd) =
      instruction.Data (Data.«MultiplyAddSub@64»
        ((1 : BitVec 64), (false, (rm, (ra, (rn, rd)))))) := by
  simp only [arm8MultiplyAddSubWord, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  simp [holV2w_one_false, holV2w_five]

/-- `Run` of `MultiplyAddSub@64`: write `Ra + Rn * Rm` (or the difference when
`sub_op` is set) to `Rd`. -/
theorem arm8Run_multiplyAddSub (o0 : Bool) (rm ra rn rd : BitVec 5) (st : arm8_state) :
    Run (instruction.Data (Data.«MultiplyAddSub@64» ((1 : BitVec 64), (o0, (rm, (ra, (rn, rd))))))) st =
      «write'X» ((if o0 then X (TN := 64) ra st - X (TN := 64) rn st * X (TN := 64) rm st
        else X (TN := 64) ra st + X (TN := 64) rn st * X (TN := 64) rm st), rd) st := by
  simp only [Run, «dfn'MultiplyAddSub»]

end Flapjack.Compiler.Encoders.Arm8.L3
