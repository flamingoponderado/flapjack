import Flapjack.Compiler.Backend.Semantics.StackSem.JumpLower

/-! Kernel replay of all eight original HOL observations in
`scripts/hol-probes/stacksem_jumplower_probe.out`. The concrete `evaluate` stub
reproduces the HOL sub-evaluations for the programs stored in the fixture code
map; the observer records result, clock, register 1 and stack length over an
arbitrary base state with every observed field overridden. -/

namespace Flapjack.Test.StackSemJumpLowerParity

open Flapjack.StackSemJumpLower Flapjack.StackSemStateOps
open Flapjack.Compiler.Backend.StackLang

/-- Concrete sub-evaluator reproducing the HOL `evaluate` results for the
fixture programs `Skip`, `Return`, `Break`, and `Continue`. -/
def evaluateStub {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  match prog with
  | .skip => (none, s)
  | .ret n =>
      match getVar n s with
      | some (.loc l1 l2) => (some (.result (.loc l1 l2)), s)
      | _ => (some .error, s)
  | .break n => (some (.break n), s)
  | .continue n => (some (.continue n), s)
  | _ => (some .error, s)

private def fixture {C F : Type} (s : StackSemStateFiniteExact 8 C F) :
    StackSemStateFiniteExact 8 C F :=
  { s with
    clock := 5
    regs := (((HolFiniteMapExact.empty : HolFiniteMapExact Nat (WordLocW 8)).updateEq
      (1, .word 3)).updateEq (2, .word 7)).updateEq (4, .loc 4 5)
    stack := [.word 9]
    code := sptInsert 10 (.ret 4) (sptInsert 12 (.break 2)
      (sptInsert 13 (.continue 3) (sptInsert 14 (.skip : HolProg 8) .ln))) }

private def observe {C F : Type}
    (result : Option (StackSemResult 8) × StackSemStateFiniteExact 8 C F) :
    Option (StackSemResult 8) × Nat × Option (WordLocW 8) × Nat :=
  (result.1, result.2.clock, result.2.regs.lookup 1, result.2.stack.length)

variable {C F : Type} (s : StackSemStateFiniteExact 8 C F)

-- jump_lower_success=(SOME (Result (Loc 4 5)),4,SOME (Word 3w),1)
example : observe (evaluateJumpLower (evaluateStub (C := C) (F := F)) 1 2 10
    (fixture s)) = (some (.result (.loc 4 5)), 4, some (.word 3), 1) := by cbv

-- jump_lower_timeout=(SOME TimeOut,0,NONE,0)
example : observe (evaluateJumpLower (evaluateStub (C := C) (F := F)) 1 2 10
    { fixture s with clock := 0 }) = (some .timeOut, 0, none, 0) := by cbv

-- jump_lower_code_missing=(SOME Error,5,SOME (Word 3w),1)
example : observe (evaluateJumpLower (evaluateStub (C := C) (F := F)) 1 2 11
    (fixture s)) = (some .error, 5, some (.word 3), 1) := by cbv

-- jump_lower_comparison_false=(NONE,5,SOME (Word 3w),1)
example : observe (evaluateJumpLower (evaluateStub (C := C) (F := F)) 2 1 10
    (fixture s)) = (none, 5, some (.word 3), 1) := by cbv

-- jump_lower_loc_operand=(SOME Error,5,SOME (Word 3w),1)
example : observe (evaluateJumpLower (evaluateStub (C := C) (F := F)) 4 2 10
    (fixture s)) = (some .error, 5, some (.word 3), 1) := by cbv

-- jump_lower_break_sub=(SOME Error,4,SOME (Word 3w),1)
example : observe (evaluateJumpLower (evaluateStub (C := C) (F := F)) 1 2 12
    (fixture s)) = (some .error, 4, some (.word 3), 1) := by cbv

-- jump_lower_continue_sub=(SOME Error,4,SOME (Word 3w),1)
example : observe (evaluateJumpLower (evaluateStub (C := C) (F := F)) 1 2 13
    (fixture s)) = (some .error, 4, some (.word 3), 1) := by cbv

-- jump_lower_none_sub=(SOME Error,4,SOME (Word 3w),1)
example : observe (evaluateJumpLower (evaluateStub (C := C) (F := F)) 1 2 14
    (fixture s)) = (some .error, 4, some (.word 3), 1) := by cbv

/-! Closed helper checks: `bad_fun_return` classifies exactly `NONE` and
`Break`/`Continue`, and the unsigned `Lower` comparison distinguishes the two
operand orders used by the successful and false-comparison rows. -/
private def checks : Bool :=
  Flapjack.StackSemControl.badFunReturn (none : Option (StackSemResult 8)) &&
  Flapjack.StackSemControl.badFunReturn (some (.break 2) : Option (StackSemResult 8)) &&
  Flapjack.StackSemControl.badFunReturn (some (.continue 3) : Option (StackSemResult 8)) &&
  !Flapjack.StackSemControl.badFunReturn (some (.result (.loc 4 5)) : Option (StackSemResult 8)) &&
  !Flapjack.StackSemControl.badFunReturn (some .error : Option (StackSemResult 8)) &&
  !Flapjack.StackSemControl.badFunReturn (some .timeOut : Option (StackSemResult 8)) &&
  Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (3 : BitVec 8) 7 &&
  !Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (7 : BitVec 8) 3

#guard checks

def runChecks : IO Bool := do
  if checks then
    IO.println "PASS exact StackSem JumpLower fragment matches original HOL branches"
    pure true
  else
    IO.println "FAIL exact StackSem JumpLower fragment differs from original HOL branches"
    pure false

end Flapjack.Test.StackSemJumpLowerParity
