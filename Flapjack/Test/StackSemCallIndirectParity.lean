import Flapjack.Compiler.Backend.Semantics.StackSem.Call
import Flapjack.Compiler.Backend.Semantics.StackSem.LeafTransfers

/-! Replay of ten direct original HOL `evaluate` observations in
`stacksem_call_indirect_probe.out` (find_code645-651 and Call861-892).
The recursive callback uses the actual `evaluateLeaf` fragment; all reached
callees and continuations are Return3/Return4, handled by that fragment.
The fallback is a test marker for unsupported programs and is never reached.
This test callback is not a total HOL evaluator; neither this fixture nor the
Call fragment closes the total evaluate_def assembly bead.
Only result, clock, link register3, indirect target register4 and stack length
are compared, exactly as projected by the original HOL probe. -/
namespace Flapjack.Test.StackSemCallIndirectParity
open Flapjack Flapjack.StackSemCall Flapjack.StackSemStateOps
open Flapjack.Compiler.Backend.StackLang

private abbrev State := StackSemStateFiniteExact 8 Unit Unit
private abbrev W := WordLocW 8

private def leafEvaluate (program : HolProg 8) (state : State) :
    Option (StackSemResult 8) × State :=
  (Flapjack.StackSemLeafTransfers.evaluateLeaf program state).getD (some .error, state)

private def s0 : State where
  regs := (((HolFiniteMapExact.empty : HolFiniteMapExact Nat W).updateEq
    (1, .word 3)).updateEq (3, .loc 10 0)).updateEq (4, .loc 10 0)
  fpRegs := HolFiniteMapExact.empty
  store := HolFiniteMapExact.empty
  stack := [.word 9]
  stackSpace := 0
  memory := fun _ => .word 0
  mdomain := fun _ => false
  shMdomain := fun _ => false
  bitmaps := []
  compile := fun _ _ => none
  compileOracle := fun _ => ((), [], [])
  codeBuffer := { position := 0, buffer := [], spaceLeft := 0 }
  dataBuffer := { position := 0, buffer := [], spaceLeft := 0 }
  gcFun := fun _ => none
  useStack := false
  useStore := false
  useAlloc := false
  clock := 5
  code := sptInsert 10 (.ret 3) .ln
  ffi := { oracle := fun _ _ _ _ => .final .diverged, ffiState := (), ioEvents := [] }
  ffiSaveRegs := fun _ => false
  be := false

private inductive RView where
  | result (first second : Nat)
  | error
  | timeOut
  | other
  deriving DecidableEq

private def resultView : Option (StackSemResult 8) → RView
  | some (.result (.loc first second)) => .result first second
  | some .error => .error
  | some .timeOut => .timeOut
  | _ => .other

private def observe (rs : Option (StackSemResult 8) × State) :
    RView × Nat × Option W × Option W × Nat :=
  (resultView rs.1, rs.2.clock, rs.2.regs.lookup 3, rs.2.regs.lookup 4, rs.2.stack.length)

-- The outer dispatch handles every actual callee/continuation in this probe.
example (state : State) : (Flapjack.StackSemLeafTransfers.evaluateLeaf (.ret 3) state).isSome = true := by
  simp only [Flapjack.StackSemLeafTransfers.evaluateLeaf_ret, Option.isSome_some]
example (state : State) : (Flapjack.StackSemLeafTransfers.evaluateLeaf (.ret 4) state).isSome = true := by
  simp only [Flapjack.StackSemLeafTransfers.evaluateLeaf_ret, Option.isSome_some]

-- indirect_tail
example : observe (evaluateCall leafEvaluate (none) (.inr 4) none (s0)) = (.result 10 0, 4, some (.loc 10 0), some (.loc 10 0), 1) := by cbv

-- indirect_return
example : observe (evaluateCall leafEvaluate (some (.ret 3, 3, 7, 8)) (.inr 4) none (s0)) = (.result 7 8, 4, some (.loc 7 8), some (.loc 10 0), 1) := by cbv

-- indirect_link_alias
example : observe (evaluateCall leafEvaluate (some (.ret 3, 3, 7, 8)) (.inr 3) none (s0)) = (.error, 5, some (.loc 10 0), some (.loc 10 0), 1) := by cbv

-- indirect_tail_alias
example : observe (evaluateCall leafEvaluate (none) (.inr 3) none (s0)) = (.result 10 0, 4, some (.loc 10 0), some (.loc 10 0), 1) := by cbv

-- indirect_nonzero
example : observe (evaluateCall leafEvaluate (some (.ret 3, 3, 7, 8)) (.inr 4) none ({ s0 with regs := s0.regs.updateEq (4, .loc 10 1) })) = (.error, 5, some (.loc 10 0), some (.loc 10 1), 1) := by cbv

-- indirect_word
example : observe (evaluateCall leafEvaluate (some (.ret 3, 3, 7, 8)) (.inr 4) none ({ s0 with regs := s0.regs.updateEq (4, .word 10) })) = (.error, 5, some (.loc 10 0), some (.word 10), 1) := by cbv

-- indirect_missing
example : observe (evaluateCall leafEvaluate (some (.ret 3, 3, 7, 8)) (.inr 4) none ({ s0 with regs := s0.regs.eraseEq 4 })) = (.error, 5, some (.loc 10 0), none, 1) := by cbv

-- indirect_code_missing
example : observe (evaluateCall leafEvaluate (some (.ret 3, 3, 7, 8)) (.inr 4) none ({ s0 with regs := s0.regs.updateEq (4, .loc 20 0) })) = (.error, 5, some (.loc 10 0), some (.loc 20 0), 1) := by cbv

-- indirect_timeout
example : observe (evaluateCall leafEvaluate (some (.ret 3, 3, 7, 8)) (.inr 4) none ({ s0 with clock := 0 })) = (.timeOut, 0, none, none, 0) := by cbv

-- indirect_wrong_return
example : observe (evaluateCall leafEvaluate (some (.ret 3, 3, 7, 8)) (.inr 4) none ({ s0 with code := sptInsert 10 (.ret 4) .ln })) = (.error, 4, some (.loc 7 8), some (.loc 10 0), 1) := by cbv

/-- Runtime observations of exactly the ten captured original rows. -/
def rows : List (String × Bool) :=
  [("indirect_tail", decide (observe (evaluateCall leafEvaluate (none) (.inr 4) none (s0)) = (.result 10 0, 4, some (.loc 10 0), some (.loc 10 0), 1))),
   ("indirect_return", decide (observe (evaluateCall leafEvaluate (some (.ret 3, 3, 7, 8)) (.inr 4) none (s0)) = (.result 7 8, 4, some (.loc 7 8), some (.loc 10 0), 1))),
   ("indirect_link_alias", decide (observe (evaluateCall leafEvaluate (some (.ret 3, 3, 7, 8)) (.inr 3) none (s0)) = (.error, 5, some (.loc 10 0), some (.loc 10 0), 1))),
   ("indirect_tail_alias", decide (observe (evaluateCall leafEvaluate (none) (.inr 3) none (s0)) = (.result 10 0, 4, some (.loc 10 0), some (.loc 10 0), 1))),
   ("indirect_nonzero", decide (observe (evaluateCall leafEvaluate (some (.ret 3, 3, 7, 8)) (.inr 4) none ({ s0 with regs := s0.regs.updateEq (4, .loc 10 1) })) = (.error, 5, some (.loc 10 0), some (.loc 10 1), 1))),
   ("indirect_word", decide (observe (evaluateCall leafEvaluate (some (.ret 3, 3, 7, 8)) (.inr 4) none ({ s0 with regs := s0.regs.updateEq (4, .word 10) })) = (.error, 5, some (.loc 10 0), some (.word 10), 1))),
   ("indirect_missing", decide (observe (evaluateCall leafEvaluate (some (.ret 3, 3, 7, 8)) (.inr 4) none ({ s0 with regs := s0.regs.eraseEq 4 })) = (.error, 5, some (.loc 10 0), none, 1))),
   ("indirect_code_missing", decide (observe (evaluateCall leafEvaluate (some (.ret 3, 3, 7, 8)) (.inr 4) none ({ s0 with regs := s0.regs.updateEq (4, .loc 20 0) })) = (.error, 5, some (.loc 10 0), some (.loc 20 0), 1))),
   ("indirect_timeout", decide (observe (evaluateCall leafEvaluate (some (.ret 3, 3, 7, 8)) (.inr 4) none ({ s0 with clock := 0 })) = (.timeOut, 0, none, none, 0))),
   ("indirect_wrong_return", decide (observe (evaluateCall leafEvaluate (some (.ret 3, 3, 7, 8)) (.inr 4) none ({ s0 with code := sptInsert 10 (.ret 4) .ln })) = (.error, 4, some (.loc 7 8), some (.loc 10 0), 1)))]

#guard rows.length == 10
#guard rows.all (·.2)

def runChecks : IO Bool := do
  let bad := rows.filter (fun row => !row.2)
  if bad.isEmpty && rows.length == 10 then
    IO.println "PASS StackSem indirect Call/link-register fragment matches 10 original HOL rows"
    pure true
  else
    IO.println s!"FAIL StackSem indirect Call original rows: {bad.map (·.1)}"
    pure false
end Flapjack.Test.StackSemCallIndirectParity
