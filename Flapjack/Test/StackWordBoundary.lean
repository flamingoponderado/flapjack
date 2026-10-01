import Flapjack.Compiler.Backend.StackLang.ProductionWordBoundary

namespace Flapjack.Test.StackWordBoundary
open Flapjack Flapjack.Compiler.Backend.StackLang

-- Distinct structural positions are retained; only the immediate changes.
example : natToWord (width := 8) (.inst (.memOffset .store8 2 3 511)) =
    .inst (.memOffset .store8 2 3 255) := by simp [natToWord, mapWordPayloads, mapInstPayloads]
example : natToWord (width := 1) (.shMemOffset .store 2 3 5) =
    .shMemOffset .store 2 3 1 := by simp [natToWord, mapWordPayloads]
example : natToWord (width := 8) (.const 2 511) = .const 2 511 := by
  simp [natToWord, mapWordPayloads]
example : natToWord (width := 8) (.stackStore 2 511) = .stackStore 2 511 := by
  simp [natToWord, mapWordPayloads]
example : natToWord (width := 8) (.inst (.arith (.binOp .xor 2 3 (.imm 511)))) =
    .inst (.arith (.binOp .xor 2 3 (.imm 255))) := by
  simp [natToWord, mapWordPayloads, mapInstPayloads, mapArithPayloads, mapRegImmPayloads]
example : natToWord (width := 8) (.inst (.arith (.shift .ror 2 3 (.reg 511)))) =
    .inst (.arith (.shift .ror 2 3 (.reg 511))) := by
  simp [natToWord, mapWordPayloads, mapInstPayloads, mapArithPayloads, mapRegImmPayloads]
example : natToWord (width := 80) (.inst (.const 2 (2 ^ 79 + 1))) =
    .inst (.const 2 (BitVec.ofNat 80 (2 ^ 79 + 1))) := by
  simp [natToWord, mapWordPayloads, mapInstPayloads]
example : natToWord (width := 8)
    (.call (some (.inst (.const 2 511), 3, 4, 5)) (.label 6)
      (some (.shMemOffset .load 7 8 257, 9, 10))) =
    .call (some (.inst (.const 2 255), 3, 4, 5)) (.label 6)
      (some (.shMemOffset .load 7 8 1, 9, 10)) := by
  simp [natToWord, mapWordPayloads, mapInstPayloads]
example : byteNames (.ffi "ÿ" 2 3 4 5 6 : StackProg Nat) = true := by
  simp [byteNames]
example : byteNames (.ffi "Ā" 2 3 4 5 6 : StackProg Nat) = false := by
  simp [byteNames]
example : byteNames (.call (some (.skip, 2, 3, 4)) (.register 5)
    (some (.loop (.ffi "😀" 6 7 8 9 10), 11, 12)) : StackProg Nat) = false := by
  simp [byteNames]
example : natToHolProg (width := 64)
    (.seq .skip (.ffi "Ā" 2 3 4 5 6)) = none := by
  simp [natToHolProg, byteNames]
example : natToHolProg (width := 64) (.const 2 511) = none := by
  simp [natToHolProg, byteNames, natToWord, mapWordPayloads, productionToHolProg, progFromProduction]
example : natToHolProg (width := 64) (.arith .or 2 3 4) = none := by
  simp [natToHolProg, byteNames, natToWord, mapWordPayloads, productionToHolProg, progFromProduction]
example : natToHolProg (width := 64) (.shift .lsl 2 3 4) = none := by
  simp [natToHolProg, byteNames, natToWord, mapWordPayloads, productionToHolProg, progFromProduction]

end Flapjack.Test.StackWordBoundary
