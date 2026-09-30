import Flapjack.Compiler.Backend.StackProps.RegisterNames

namespace Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-- Pre-naming FP instruction admissibility. This checks only register names,
width-dependent register pairs and ISA constraints; it does not evaluate FP values. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "fp_name_def"
  (words_as_type_indexed_bitvec)]
def fpName {width : Nat} [NeZero width] (operation : HolFp)
    (config : AsmConfigExact width) : Prop :=
  match operation with
  | .fpLess r d1 d2 | .fpLessEqual r d1 d2 | .fpEqual r d1 d2 =>
      regName r config ∧ asmFpRegOkExact d1 config = true ∧ asmFpRegOkExact d2 config = true
  | .fpAbs d1 d2 | .fpNeg d1 d2 =>
      (config.twoRegArith = true → d1 ≠ d2) ∧
      asmFpRegOkExact d1 config = true ∧ asmFpRegOkExact d2 config = true
  | .fpSqrt d1 d2 | .fpMov d1 d2 | .fpToInt d1 d2 | .fpFromInt d1 d2 =>
      asmFpRegOkExact d1 config = true ∧ asmFpRegOkExact d2 config = true
  | .fpAdd d1 d2 d3 | .fpSub d1 d2 d3 | .fpMul d1 d2 d3 | .fpDiv d1 d2 d3 =>
      (config.twoRegArith = true → d1 = d2) ∧
      asmFpRegOkExact d1 config = true ∧ asmFpRegOkExact d2 config = true ∧
      asmFpRegOkExact d3 config = true
  | .fpFma d1 d2 d3 =>
      config.isa = .armv7 ∧ 2 < config.fpRegCount ∧
      asmFpRegOkExact d1 config = true ∧ asmFpRegOkExact d2 config = true ∧
      asmFpRegOkExact d3 config = true
  | .fpMovToReg r1 r2 d | .fpMovFromReg d r1 r2 =>
      regName r1 config ∧ (width = 32 → r1 ≠ r2 ∧ regName r2 config) ∧
      asmFpRegOkExact d config = true

end Flapjack.Compiler.Backend.StackProps
