import Flapjack.Compiler.Backend.Semantics.StackSem.ShMemOpCase

/-! Kernel replay of all four original HOL observations in
`scripts/hol-probes/stacksem_sh_mem_op_probe.out`. The observer records the
result, clock, FFI state, register 3 and stack length; a byte-incrementing FFI
oracle makes the successful row observable. -/

namespace Flapjack.Test.StackSemShMemOpParity

open Flapjack.StackSemShMemOpCase
open Flapjack.Compiler.Backend.StackLang

private abbrev W := WordLocW 8

private def incFfi : HolFfiState Nat :=
  { oracle := fun _ st _ bytes => .ret (st + 1) (bytes.map (· + 1)), ffiState := 0,
    ioEvents := [] }

private def s0 (clock : Nat) (regs : HolFiniteMapExact Nat W) :
    StackSemStateFiniteExact 8 Unit Nat where
  regs := regs
  fpRegs := HolFiniteMapExact.empty
  store := HolFiniteMapExact.empty
  stack := [.word 9]
  stackSpace := 0
  memory := fun _ => .word 0
  mdomain := fun _ => false
  shMdomain := fun a => a = 8
  bitmaps := []
  compile := fun _ _ => none
  compileOracle := fun _ => ((), [], [])
  codeBuffer := { position := 0, buffer := [], spaceLeft := 2 }
  dataBuffer := { position := 0, buffer := [], spaceLeft := 2 }
  gcFun := fun _ => none
  useStack := false
  useStore := false
  useAlloc := false
  clock := clock
  code := .ln
  ffi := incFfi
  ffiSaveRegs := fun _ => false
  be := false

private def proj
    (r : Option (Option (StackSemResult 8) × StackSemStateFiniteExact 8 Unit Nat)) :
    Option (Option (StackSemResult 8) × Nat × Nat × Option W × Nat) :=
  r.map (fun p => (p.1, p.2.clock, p.2.ffi.ffiState, p.2.regs.lookup 3, p.2.stack.length))

private def reg3 (x : W) : HolFiniteMapExact Nat W :=
  (HolFiniteMapExact.empty : HolFiniteMapExact Nat W).updateEq (3, x)

-- sh_mem_op_success=(NONE,4,1,SOME (Word 0w),1)
example : proj (evaluateShMemOp (.shMemOp .load 5 (.addr 3 8)) (s0 5 (reg3 (.word 0)))) =
    some (none, 4, 1, some (.word 0), 1) := by cbv

-- sh_mem_op_word_exp_none=(SOME Error,5,0,SOME (Loc 1 0),1)
example : proj (evaluateShMemOp (.shMemOp .load 5 (.addr 3 8)) (s0 5 (reg3 (.loc 1 0)))) =
    some (some .error, 5, 0, some (.loc 1 0), 1) := by cbv

-- sh_mem_op_missing_register=(SOME Error,5,0,NONE,1)
example : proj (evaluateShMemOp (.shMemOp .load 5 (.addr 3 8))
      (s0 5 HolFiniteMapExact.empty)) =
    some (some .error, 5, 0, none, 1) := by cbv

-- sh_mem_op_timeout=(SOME TimeOut,0,0,NONE,0)
example : proj (evaluateShMemOp (.shMemOp .load 5 (.addr 3 8)) (s0 0 (reg3 (.word 0)))) =
    some (some .timeOut, 0, 0, none, 0) := by cbv

/-! Closed helper checks: the effective address `0 + 8` reaches 8 at width 8 and
`dec_clock` subtracts one from a positive clock, matching the successful and
timeout rows. -/
private def checks : Bool :=
  ((0 : BitVec 8) + 8 == 8) && ((5 : Nat) - 1 == 4)

#guard checks

def runChecks : IO Bool := do
  if checks then
    IO.println "PASS exact StackSem ShMemOp evaluate clause matches all 4 HOL rows"
    pure true
  else
    IO.println "FAIL exact StackSem ShMemOp evaluate clause differs from HOL rows"
    pure false

end Flapjack.Test.StackSemShMemOpParity
