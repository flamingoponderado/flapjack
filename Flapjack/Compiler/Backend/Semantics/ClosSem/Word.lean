import Flapjack.Compiler.Backend.Semantics.ClosSem
import Flapjack.SemanticPrimitivesHOL.Compare
import Flapjack.FpSemHOL

/-! Word and floating-point operations for closure semantics. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL

/-- Word arithmetic selected by the closure operator. -/
def applyWordOp {width : Nat} (op : BackendCommon.Opw) (a b : BitVec width) : BitVec width :=
  match op with
  | .andw => a &&& b
  | .orw => a ||| b
  | .xor => a ^^^ b
  | .add => a + b
  | .sub => a - b

/-- Decode the unique byte represented by a nonnegative integer below 256. -/
def intToByte (n : Int) : Option (BitVec 8) :=
  if 0 ≤ n ∧ n < 256 then some (BitVec.ofInt 8 n) else none

/-- Encoding a byte as an integer and decoding it recovers that byte. -/
theorem intToByte_toNat (byte : BitVec 8) : intToByte (byte.toNat : Int) = some byte := by
  have bound : byte.toNat < 256 := by simpa using byte.isLt
  simp [intToByte]
  exact Int.ofNat_lt.mpr bound

/-- Integer and fixed-word cases of the closure word dispatcher. -/
def doWordAppIntegral : ClosLang.WordOp → List Value → Option Value
  | .wordOpw .w8 op, [.number a, .number b] => do
    let x ← intToByte a
    let y ← intToByte b
    pure (.number (applyWordOp op x y).toNat)
  | .wordOpw .w64 op, [.word64 a, .word64 b] => some (.word64 (applyWordOp op a b))
  | .wordTest .w8 test, [.number a, .number b] =>
    if 0 ≤ a ∧ a < 256 ∧ 0 ≤ b ∧ b < 256 then
      match test with
      | .equal => some (boolValue (decide (a = b)))
      | .compare op => some (boolValue (intCmp op a b))
      | .altCompare _ => none
    else none
  | .wordShift .w8 shift amount, [.number n] => do
    let word ← intToByte n
    pure (.number (shift8Lookup shift word amount).toNat)
  | .wordShift .w64 shift amount, [.word64 word] =>
    some (.word64 (shift64Lookup shift word amount))
  | .wordFromInt, [.number n] => some (.word64 (BitVec.ofInt 64 n))
  | .wordToInt, [.word64 word] => some (.number word.toNat)
  | .wordFromWord true, [.word64 word] => some (.number (BitVec.ofNat 8 word.toNat).toNat)
  | .wordFromWord false, [.number n] => do
    let byte ← intToByte n
    pure (.word64 (BitVec.ofNat 64 byte.toNat))
  | _, _ => none

/-- Full closure word dispatcher, including the existing floating-point
model. This remains untagged pending source and carrier review; floating-point
cases inherit the rational-cut assumptions of `FpSemHOL`. -/
noncomputable def doWordApp (op : ClosLang.WordOp) (values : List Value) : Option Value :=
  match op, values with
  | .fpTop op, [.word64 a, .word64 b, .word64 c] => some (.word64 (fpSemFpTopComp op a b c))
  | .fpBop op, [.word64 a, .word64 b] => some (.word64 (fpSemFpBopComp op a b))
  | .fpUop op, [.word64 a] => some (.word64 (fpSemFpUopComp op a))
  | .fpCmp op, [.word64 a, .word64 b] => some (boolValue (fpSemFpCmpComp op a b))
  | _, _ => doWordAppIntegral op values

end Flapjack.Compiler.Backend.ClosSem
