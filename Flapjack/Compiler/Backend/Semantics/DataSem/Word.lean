import Flapjack.Compiler.Backend.Semantics.DataSem.Value
import Flapjack.Compiler.Backend.Semantics.ClosSem.Word

/-! Word and floating-point primitives of the data-language semantics. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL

/-- The integer and fixed-word clauses of the data-language dispatcher.
The byte conversion implements the unique-word condition in the original. -/
def doWordAppIntegral : ClosLang.WordOp → List Value → Option Value
  | .wordOpw .w8 op, [.number a, .number b] => do
    let x ← ClosSem.intToByte a
    let y ← ClosSem.intToByte b
    pure (.number (ClosSem.applyWordOp op x y).toNat)
  | .wordOpw .w64 op, [.word64 a, .word64 b] => some (.word64 (ClosSem.applyWordOp op a b))
  | .wordTest .w8 test, [.number a, .number b] =>
    if 0 ≤ a ∧ a < 256 ∧ 0 ≤ b ∧ b < 256 then
      match test with
      | .equal => some (boolValue (decide (a = b)))
      | .compare .lt => some (boolValue (decide (a < b)))
      | .compare .leq => some (boolValue (decide (a ≤ b)))
      | _ => none
    else none
  | .wordShift .w8 shift amount, [.number n] => do
    let word ← ClosSem.intToByte n
    pure (.number (shift8Lookup shift word amount).toNat)
  | .wordShift .w64 shift amount, [.word64 word] =>
    some (.word64 (shift64Lookup shift word amount))
  | .wordFromInt, [.number n] => some (.word64 (BitVec.ofInt 64 n))
  | .wordToInt, [.word64 word] => some (.number word.toNat)
  | .wordFromWord true, [.word64 word] => some (.number (BitVec.ofNat 8 word.toNat).toNat)
  | .wordFromWord false, [.number n] => do
    let byte ← ClosSem.intToByte n
    pure (.word64 (BitVec.ofNat 64 byte.toNat))
  | _, _ => none

/-- Data-language word dispatcher, including the floating-point clauses. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "do_word_app_def"]
noncomputable def doWordApp (op : ClosLang.WordOp) (values : List Value) : Option Value :=
  match op, values with
  | .fpTop op, [.word64 a, .word64 b, .word64 c] => some (.word64 (fpSemFpTopComp op a b c))
  | .fpBop op, [.word64 a, .word64 b] => some (.word64 (fpSemFpBopComp op a b))
  | .fpUop op, [.word64 a] => some (.word64 (fpSemFpUopComp op a))
  | .fpCmp op, [.word64 a, .word64 b] => some (boolValue (fpSemFpCmpComp op a b))
  | _, _ => doWordAppIntegral op values

end Flapjack.Compiler.Backend.DataSem
