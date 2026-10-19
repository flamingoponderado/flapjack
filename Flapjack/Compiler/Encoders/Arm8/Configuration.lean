import Flapjack.Compiler.Encoders.Arm8.Target

/-! The ARMv8 assembler configuration (`arm8_config` of
`cakeml/compiler/encoders/arm8/arm8_targetScript.sml`), over the subset encoder in
`Flapjack.Compiler.Encoders.Arm8.Target`.

The `encode` field is `arm8Enc` over Flapjack's `HolAsm 64` carrier rather than HOL's
full L3 `arm8$instruction`, so this record is not tagged as an exact `arm8_config` port.
All bounds are the original ones; `valid_immediate` uses `EncodeBitMask`. -/
namespace Flapjack.Compiler.Encoders.Arm8
open Flapjack Compiler.Encoders.Asm

/-- Closed-model counterpart of `valid_immediate`: the integer-range test for
`Add`/`Sub`/`Less`/`Lower`/`Equal`/`NotLess`/`NotLower`/`NotEqual`, and
`EncodeBitMask` for the bitwise operations.  Deliberately untagged:
`encodeBitMask` is Flapjack's `Nat`-valued rendering of L3's `EncodeBitMask`, so
this declaration has not been reviewed as an exact carrier-level HOL port. -/
def validImmediate (operator : Sum BinOp Cmp) (i : BitVec 64) : Bool :=
  match operator with
  | .inl .add | .inl .sub
  | .inr .less | .inr .lower | .inr .equal
  | .inr .notLess | .inr .notLower | .inr .notEqual =>
      (i &&& ~~~(0xFFF : BitVec 64) = 0) || (i &&& ~~~(0xFFF000 : BitVec 64) = 0)
  | _ => (encodeBitMask i).isSome

/-- The ARMv8 assembler configuration. -/
def arm8Config : AsmConfigExact 64 where
  isa := .armv8
  encode := arm8Enc
  regCount := 32
  avoidRegs := [18, 26, 31]
  fpRegCount := 0
  linkReg := some 30
  twoRegArith := false
  bigEndian := false
  validImm := validImmediate
  addrOffset := (-4351, 4350)
  hwOffset := (-4351, 4350)
  byteOffset := (-256, 4095)
  jumpOffset := (-134217728, 134217727)
  cjumpOffset := (-1048572, 1048579)
  locOffset := (-2147483648, 2147483647)
  codeAlignment := 2

/-- Derived projection of the whole source record; there is no separately named HOL
theorem for this definitional field equality. -/
theorem arm8Config_encode : arm8Config.encode = arm8Enc := rfl

end Flapjack.Compiler.Encoders.Arm8
