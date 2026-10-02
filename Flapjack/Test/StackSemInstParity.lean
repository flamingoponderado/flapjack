import Flapjack.Compiler.Backend.Semantics.StackSem.InstCase

/-! Kernel replay of all six original HOL observations in
`scripts/hol-probes/stacksem_inst_probe.out`. The fixture overrides every
observed field over an arbitrary base state; each row calls the untagged
`evaluateInst` fragment and compares the result, register 1 and the clock. -/

namespace Flapjack.Test.StackSemInstParity
open StackSemInstCase StackSemInst StackSemStateOps

private def fixture {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    StackSemStateFiniteExact 64 C F :=
  { s with
    clock := 6
    be := false
    memory := fun a => .word a
    mdomain := fun _ => false
    regs := (((HolFiniteMapExact.empty : HolFiniteMapExact Nat (WordLocW 64)).updateEq
      (1, .word 9)).updateEq (2, .word 5)).updateEq (4, .loc 3 0) }

private noncomputable def observe {C F : Type} :
    Option (Option (StackSemResult 64) × StackSemStateFiniteExact 64 C F) →
    Option (Option (StackSemResult 64) × Option (WordLocW 64) × Nat)
  | none => none
  | some (r, s) => some (r, s.regs.lookup 1, s.clock)

variable {C F : Type} (s : StackSemStateFiniteExact 64 C F)

attribute [local simp] observe evaluateInst fixture instHOL StackSemIntegerInstructions.instInteger
  StackSemExpressions.assign StackSemExpressions.wordExp StackSemStateOps.setVar
  StackSemStateOps.getVar StackSemStateOps.memLoad HolFiniteMapExact.lookup_updateEq FUPDATE_HOL
  wordOpHOL wordOp

-- inst_const=(NONE,SOME (Word 7w),6)
example : observe (evaluateInst (.inst (.const 1 7)) (fixture s)) =
    some (none, some (.word 7), 6) := by
  simp

-- inst_add_imm=(NONE,SOME (Word 6w),6)
example : observe (evaluateInst (.inst (.arith (.binop .add 1 2 (.imm 1)))) (fixture s)) =
    some (none, some (.word 6), 6) := by
  simp

-- inst_add_missing_reg=(SOME Error,SOME (Word 9w),6)
example : observe (evaluateInst (.inst (.arith (.binop .add 1 2 (.reg 3)))) (fixture s)) =
    some (some .error, some (.word 9), 6) := by
  simp

-- inst_add_loc=(SOME Error,SOME (Word 9w),6)
example : observe (evaluateInst (.inst (.arith (.binop .add 1 4 (.imm 1)))) (fixture s)) =
    some (some .error, some (.word 9), 6) := by
  simp

-- inst_load_outside=(SOME Error,SOME (Word 9w),6)
example : observe (evaluateInst (.inst (.mem .load 1 (.addr 2 0))) (fixture s)) =
    some (some .error, some (.word 9), 6) := by
  simp

-- inst_skip=(NONE,SOME (Word 9w),6)
example : observe (evaluateInst (.inst (.skip)) (fixture s)) =
    some (none, some (.word 9), 6) := by
  simp

-- The fragment returns the outer NONE sentinel for an unhandled constructor,
-- so it never substitutes Error for an unported clause.
example : evaluateInst (width := 64) (.skip) (fixture s) = none := rfl

def runChecks : IO Bool := do
  IO.println "PASS exact StackSem Inst fragment matches six original HOL rows"
  pure true

end Flapjack.Test.StackSemInstParity
