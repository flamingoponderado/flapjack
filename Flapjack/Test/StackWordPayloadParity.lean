import Flapjack.Compiler.Backend.StackLang.WordPayloads.InstructionBoundary

/-! Kernel checks of the shared word-payload boundary only. These examples do
not claim that the Nat-only production macros or the compiler route are exact. -/
namespace Flapjack.Test.StackWordPayloadParity
open Flapjack Compiler.Backend.StackLang.WordPayloads

example : natToWords 8 (.inst (.const 9 255)) = .inst (.const 9 255) := rfl
example : wordsToNat (natToWords 8 (.inst (.const 9 256))) =
    .inst (.const 9 0) := rfl
example : ¬ Bounded 8 (.inst (.const 9 256)) := by
  simp [Bounded, values, instValues]
example : natToWords 8 (.const 9 256) = .const 9 256 := rfl
example : Bounded 8 (.const 9 256) := by simp [Bounded, values]
example : natToWords 8 (.inst (.memOffset .store 19 20 259)) =
    .inst (.memOffset .store 19 20 3) := rfl
example : natToWords 8 (.shMemOffset .load 19 20 259) =
    .shMemOffset .load 19 20 3 := rfl
example : natToWords 8 (.inst (.arith (.binOp .add 19 20 (.imm 259)))) =
    .inst (.arith (.binOp .add 19 20 (.imm 3))) := rfl
example : natToWords 8 (.inst (.arith (.shift .lsl 19 20 (.reg 259)))) =
    .inst (.arith (.shift .lsl 19 20 (.reg 259))) := rfl
example : natToWords 8 (.ffi "λ" 259 260 261 262 263) =
    .ffi "λ" 259 260 261 262 263 := rfl

example : values
    (.call (some (.inst (.const 19 255), 256, 257, 258)) (.register 259)
      (some (.loop (.ite .equal 260 (.imm 7)
        (.shMemOffset .store 261 262 8) .skip), 263, 264)) : StackProg Nat) =
    [255, 7, 8] := rfl

example (p : StackProg (BitVec 64)) : natToWords 64 (wordsToNat p) = p :=
  natToWords_wordsToNat p
example (p : StackProg Nat) (h : Bounded 64 p) :
    wordsToNat (natToWords 64 p) = p := wordsToNat_natToWords p h
example (p : StackProg (BitVec 64)) : Bounded 64 (wordsToNat p) :=
  bounded_wordsToNat p
example (i : WordInst Nat) :
    mapInst (BitVec.ofNat 64) i = RiscV.labWordInstToWord (width := 64) i :=
  mapInst_ofNat i
example (i : WordInst (BitVec 64)) :
    mapInst BitVec.toNat i = RiscV.wordInstToNat i := mapInst_toNat i

def runChecks : IO Bool := do
  IO.println "PASS StackProg numeric word-payload boundary (bounded reverse; macros unchanged)"
  return true
end Flapjack.Test.StackWordPayloadParity
