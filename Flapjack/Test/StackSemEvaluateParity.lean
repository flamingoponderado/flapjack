import Flapjack.Compiler.Backend.Semantics.StackSem.Evaluate

/-! Kernel replay of the eleven original HOL observations of
`scripts/hol-probes/stacksem_control_probe.out` (`Seq`, `If` and `Loop` of
`stackSemScript.sml:811-837`) through the assembled total `evaluateHOL`. Unlike
`StackSemControlCasesParity`, the sub-evaluations are not stubbed: every
sub-program, including the `Loop` re-entries down to the clock-0 timeout, runs
through the evaluator itself. -/

namespace Flapjack.Test.StackSemEvaluateParity

open Flapjack.StackSemEvaluate Flapjack.StackSemControl Flapjack.StackSemStateOps
open Flapjack.StackSemLeafTransfers
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

private abbrev W := WordLocW 8

private def w8 (n : Nat) : BitVec 8 := BitVec.ofNat 8 n

/-- Probe fixture: register `1 -> Word 3w`, register `4 -> Loc 4 5`, one-word
stack, empty code, and the base state's other fields left arbitrary. -/
private def fixture {C F : Type} (s : StackSemStateFiniteExact 8 C F) :
    StackSemStateFiniteExact 8 C F :=
  { s with
    clock := 5
    regs := (((HolFiniteMapExact.empty : HolFiniteMapExact Nat W).updateEq
      (1, .word (w8 3))).updateEq (4, .loc 4 5))
    stack := [.word (w8 9)]
    code := .ln }

/-- Observed projection: result, clock, register 1, stack length. -/
private def observe {C F : Type}
    (result : Option (StackSemResult 8) × StackSemStateFiniteExact 8 C F) :
    Option (StackSemResult 8) × Nat × Option W × Nat :=
  (result.1, result.2.clock, result.2.regs.lookup 1, result.2.stack.length)

variable {C F : Type} (s : StackSemStateFiniteExact 8 C F)

attribute [local simp] observe fixture w8 evaluateHOL_seq evaluateHOL_ite evaluateHOL_loop
  evaluateHOL_skip evaluateHOL_ret evaluateHOL_halt evaluateHOL_tick evaluateHOL_break
  evaluateHOL_continue fromFragment evaluateLeaf StackSemControlCases.evaluateSeq
  StackSemControlCases.evaluateIf StackSemControlCases.evaluateLoop fixClock getVar
  HolFiniteMapExact.lookup_updateEq FUPDATE_HOL StackSemStateOps.emptyEnv StackSemStateOps.decClock
  StackSemControl.contLoop StackSemControl.exitLoop wordSemWordCmp StackSemStateOps.getVarImm
  HolRegImm.toWordRegImm wordCmpHOL

-- seq_normal=(SOME (Result (Loc 4 5)),5,SOME (Word 3w),1)
example : observe (evaluateHOL (.seq (.ret 4) (.halt 1)) (fixture s)) =
    (some (.result (.loc 4 5)), 5, some (.word (w8 3)), 1) := by
  simp

-- seq_fallthrough=(SOME (Halt (Word 3w)),5,NONE,0)
example : observe (evaluateHOL (.seq .skip (.halt 1)) (fixture s)) =
    (some (.halt (.word (w8 3))), 5, none, 0) := by
  simp

-- seq_tick_clamp=(SOME (Result (Loc 4 5)),4,SOME (Word 3w),1)
example : observe (evaluateHOL (.seq .tick (.ret 4)) (fixture s)) =
    (some (.result (.loc 4 5)), 4, some (.word (w8 3)), 1) := by
  simp

-- if_true=(SOME (Result (Loc 4 5)),5,SOME (Word 3w),1)
example : observe (evaluateHOL (.ite .equal 1 (.imm (w8 3)) (.ret 4) (.halt 1)) (fixture s)) =
    (some (.result (.loc 4 5)), 5, some (.word (w8 3)), 1) := by
  simp

-- if_false=(SOME (Halt (Word 3w)),5,NONE,0)
example : observe (evaluateHOL (.ite .equal 1 (.imm (w8 4)) (.ret 4) (.halt 1)) (fixture s)) =
    (some (.halt (.word (w8 3))), 5, none, 0) := by
  simp

-- if_cmp_none=(SOME Error,5,SOME (Word 3w),1)
example : observe (evaluateHOL (.ite .equal 4 (.imm (w8 3)) (.ret 4) (.halt 1)) (fixture s)) =
    (some .error, 5, some (.word (w8 3)), 1) := by
  simp

-- if_operand_missing=(SOME Error,5,SOME (Word 3w),1)
example : observe (evaluateHOL (.ite .equal 9 (.imm (w8 3)) (.ret 4) (.halt 1)) (fixture s)) =
    (some .error, 5, some (.word (w8 3)), 1) := by
  simp

-- loop_recurse=(SOME TimeOut,0,NONE,0)
example : observe (evaluateHOL (.loop (.continue 0)) (fixture s)) =
    (some .timeOut, 0, none, 0) := by
  simp

-- loop_timeout=(SOME TimeOut,0,NONE,0)
example : observe (evaluateHOL (.loop .skip) (fixture s)) =
    (some .timeOut, 0, none, 0) := by
  simp

-- loop_exit_break=(SOME (Break 0),5,SOME (Word 3w),1)
example : observe (evaluateHOL (.loop (.break 1)) (fixture s)) =
    (some (.break 0), 5, some (.word (w8 3)), 1) := by
  simp

-- loop_exit_continue=(SOME (Continue 0),5,SOME (Word 3w),1)
example : observe (evaluateHOL (.loop (.continue 1)) (fixture s)) =
    (some (.continue 0), 5, some (.word (w8 3)), 1) := by
  simp

def runChecks : IO Bool := do
  IO.println "PASS total StackSem evaluateHOL matches eleven original HOL Seq/If/Loop rows"
  pure true

end Flapjack.Test.StackSemEvaluateParity
