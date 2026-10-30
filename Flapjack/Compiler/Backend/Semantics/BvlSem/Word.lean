import Flapjack.Compiler.Backend.Semantics.BvlSem.Value
import Flapjack.Compiler.Backend.Semantics.ClosSem.Word

/-! BVL word and floating-point primitives. -/
namespace Flapjack.Compiler.Backend.BvlSem
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL

/-- The byte decoder implements the original unique word8 condition. -/
theorem intToByte_iff (n : Int) (byte : BitVec 8) :
    ClosSem.intToByte n = some byte ↔ n = (byte.toNat : Int) := by
  constructor
  · intro h
    simp only [ClosSem.intToByte] at h
    split at h
    · rename_i bounds
      simp only [Option.some.injEq] at h
      subst byte
      simp [BitVec.toNat_ofInt, Int.emod_eq_of_lt bounds.1 bounds.2, Int.max_eq_left bounds.1]
    · simp at h
  · intro h
    subst n
    exact ClosSem.intToByte_toNat byte

/-- Flapjack helper for the integer and fixed-word cases of the original
dispatcher. The byte decoder captures the unique word8 required by HOL. -/
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
      | .compare op => some (boolValue (intCmp op a b))
      | .altCompare _ => none
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

/-- Original word dispatcher, including floating-point operations. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "do_word_app_def"]
noncomputable def doWordApp (op : ClosLang.WordOp) (values : List Value) : Option Value :=
  match op, values with
  | .fpTop op, [.word64 a, .word64 b, .word64 c] => some (.word64 (fpSemFpTopComp op a b c))
  | .fpBop op, [.word64 a, .word64 b] => some (.word64 (fpSemFpBopComp op a b))
  | .fpUop op, [.word64 a] => some (.word64 (fpSemFpUopComp op a))
  | .fpCmp op, [.word64 a, .word64 b] => some (boolValue (fpSemFpCmpComp op a b))
  | _, _ => doWordAppIntegral op values

end Flapjack.Compiler.Backend.BvlSem
