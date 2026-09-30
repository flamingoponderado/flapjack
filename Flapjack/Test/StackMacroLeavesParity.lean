import Flapjack.Compiler.Backend.StackLang.MacroLeaves

/-! Kernel checks for isolated production macro leaves only. Seq fusion and
actual compiler route replacement remain separate obligations. -/
namespace Flapjack.Test.StackMacroLeavesParity
open Flapjack Flapjack.RiscV Compiler.Backend.StackLang.MacroLeaves

example : project 8 (.const 9 255) = some (.inst (.const 9 255)) := rfl
example : project 8 (.const 9 256) = none := rfl
example : project 64 (.arith .add 9 10 11) =
    some (.inst (.arith (.binOp .add 9 10 (.reg 11)))) := rfl
example : project 64 (.shift .ror 9 10 11) =
    some (.inst (.arith (.shift .ror 9 10 (.reg 11)))) := rfl
example : project 64 .skip = none := rfl
example : project 64 (.seq (.const 9 1) (.arith .add 9 9 10)) = none := rfl

example (d v : Nat) (h : v < 2 ^ 64) :
    labCompilePlain (width := 64) (.const d v) =
      labCompilePlain (.word (.const d (BitVec.ofNat 64 v))) := const_emission d v h
example (op : BinOp) (d l r : Nat) :
    labCompilePlain (width := 64) (.arith op d l r) =
      labCompilePlain (.word (.arith (.binOp op d l (.reg r)))) := arith_emission op d l r
example (op : Shift) (d l r : Nat) :
    labCompilePlain (width := 64) (.shift op d l r) =
      labCompilePlain (.word (.arith (.shift op d l (.reg r)))) := shift_emission op d l r

example : labCompilePlain (width := 64) (.arith .add 32 1 2) = none := rfl
example : labCompilePlain (width := 64) (.shift .ror 31 1 2) = none := rfl
example : labCompilePlain (width := 64) (.shift .ror 1 31 2) = none := rfl
example : labCompilePlain (width := 64) (.shift .ror 1 2 31) = none := rfl
example : labLineInstructionCount (width := 64) (.asm (.shift .ror 1 2 3) [] 0) = 5 := rfl
example (v : Nat) (h : v < 2 ^ 64) :
    labLineInstructionCount (width := 64) (.asm (.const 9 v) [] 0) =
      labLineInstructionCount (width := 64)
        (.asm (.word (.const 9 (BitVec.ofNat 64 v))) [] 0) := const_length 9 v h
example (op : BinOp) :
    labLineInstructionCount (width := 64) (.asm (.arith op 1 2 3) [] 0) =
      labLineInstructionCount (width := 64)
        (.asm (.word (.arith (.binOp op 1 2 (.reg 3)))) [] 0) := arith_length op 1 2 3
example (op : Shift) :
    labLineInstructionCount (width := 64) (.asm (.shift op 1 2 3) [] 0) =
      labLineInstructionCount (width := 64)
        (.asm (.word (.arith (.shift op 1 2 (.reg 3)))) [] 0) := shift_length op 1 2 3

def runChecks : IO Bool := do
  IO.println "PASS isolated Stack macro projection, emission/errors and lengths (Seq fusion open)"
  return true
end Flapjack.Test.StackMacroLeavesParity
