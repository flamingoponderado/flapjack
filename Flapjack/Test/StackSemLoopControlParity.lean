import Flapjack.Compiler.Backend.Semantics.StackSem.Control
import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps

/-! Kernel replay of all 28 original HOL observations in
`scripts/hol-probes/stacksem_loop_control_probe.out`. The lookup fixture
overrides every observed field; the final-event rows quantify over the payload.
The runtime suite also checks the eleven closed control inputs. -/

namespace Flapjack.Test.StackSemLoopControlParity

open StackSemControl StackSemStateOps

private def fixture {C F : Type} (s : StackSemStateFiniteExact 8 C F) :=
  { s with regs :=
      ((HolFiniteMapExact.empty : HolFiniteMapExact Nat (WordLocW 8)).updateEq
        (1, .word 7)).updateEq (2, .loc 4 5) }

variable {C F : Type} (s : StackSemStateFiniteExact 8 C F)

-- reg_word=SOME (Word 7w)
example : StackSemStateOps.getVarImm (.reg 1) (fixture s) = some (.word 7) := by cbv
-- reg_loc=SOME (Loc 4 5)
example : StackSemStateOps.getVarImm (.reg 2) (fixture s) = some (.loc 4 5) := by cbv
-- reg_missing=NONE
example : StackSemStateOps.getVarImm (.reg 3) (fixture s) = none := by cbv
-- immediate=SOME (Word 255w)
example : StackSemStateOps.getVarImm (.imm 255) (fixture s) = some (.word 255) := by cbv

-- cont_none=T
example : StackSemControl.contLoop (none : Option (StackSemResult 8)) = true := by decide
-- cont_continue_zero=T
example : StackSemControl.contLoop (some (.continue 0) : Option (StackSemResult 8)) = true := by decide
-- cont_continue_three=F
example : StackSemControl.contLoop (some (.continue 3) : Option (StackSemResult 8)) = false := by decide
-- cont_break_zero=F
example : StackSemControl.contLoop (some (.break 0) : Option (StackSemResult 8)) = false := by decide
-- cont_break_one=F
example : StackSemControl.contLoop (some (.break 1) : Option (StackSemResult 8)) = false := by decide
-- cont_break_three=F
example : StackSemControl.contLoop (some (.break 3) : Option (StackSemResult 8)) = false := by decide
-- cont_result=F
example : StackSemControl.contLoop (some (.result (.loc 4 5)) : Option (StackSemResult 8)) = false := by decide
-- cont_exception=F
example : StackSemControl.contLoop (some (.exception (.loc 4 5)) : Option (StackSemResult 8)) = false := by decide
-- cont_halt=F
example : StackSemControl.contLoop (some (.halt (.word 7)) : Option (StackSemResult 8)) = false := by decide
-- cont_timeout=F
example : StackSemControl.contLoop (some .timeOut : Option (StackSemResult 8)) = false := by decide
-- cont_error=F
example : StackSemControl.contLoop (some .error : Option (StackSemResult 8)) = false := by decide
-- cont_final=F
example (event : HolFinalEvent) :
    StackSemControl.contLoop (some (.finalFFI event) : Option (StackSemResult 8)) = false := rfl

-- exit_none=NONE
example : StackSemControl.exitLoop (none : Option (StackSemResult 8)) = none := rfl
-- exit_continue_zero=SOME (Continue 0)
example : StackSemControl.exitLoop (some (.continue 0) : Option (StackSemResult 8)) = some (.continue 0) := rfl
-- exit_continue_three=SOME (Continue 2)
example : StackSemControl.exitLoop (some (.continue 3) : Option (StackSemResult 8)) = some (.continue 2) := rfl
-- exit_break_zero=NONE
example : StackSemControl.exitLoop (some (.break 0) : Option (StackSemResult 8)) = none := rfl
-- exit_break_one=SOME (Break 0)
example : StackSemControl.exitLoop (some (.break 1) : Option (StackSemResult 8)) = some (.break 0) := rfl
-- exit_break_three=SOME (Break 2)
example : StackSemControl.exitLoop (some (.break 3) : Option (StackSemResult 8)) = some (.break 2) := rfl
-- exit_result=SOME (Result (Loc 4 5))
example : StackSemControl.exitLoop (some (.result (.loc 4 5)) : Option (StackSemResult 8)) = some (.result (.loc 4 5)) := rfl
-- exit_exception=SOME (Exception (Loc 4 5))
example : StackSemControl.exitLoop (some (.exception (.loc 4 5)) : Option (StackSemResult 8)) = some (.exception (.loc 4 5)) := rfl
-- exit_halt=SOME (Halt (Word 7w))
example : StackSemControl.exitLoop (some (.halt (.word 7)) : Option (StackSemResult 8)) = some (.halt (.word 7)) := rfl
-- exit_timeout=SOME TimeOut
example : StackSemControl.exitLoop (some .timeOut : Option (StackSemResult 8)) = some .timeOut := rfl
-- exit_error=SOME Error
example : StackSemControl.exitLoop (some .error : Option (StackSemResult 8)) = some .error := rfl
-- exit_final=T (equality with the unchanged original event)
example (event : HolFinalEvent) :
    StackSemControl.exitLoop (some (.finalFFI event) : Option (StackSemResult 8)) = some (.finalFFI event) := rfl

private def observe : Option (StackSemResult 8) → Nat × Nat
  | none => (0, 0)
  | some (.continue n) => (1, n)
  | some (.break n) => (2, n)
  | some (.result (.loc a b)) => (3, a * 100 + b)
  | some (.exception (.loc a b)) => (4, a * 100 + b)
  | some (.halt (.word w)) => (5, w.toNat)
  | some .timeOut => (6, 0)
  | some .error => (7, 0)
  | _ => (8, 0)

private def inputs : List (Option (StackSemResult 8)) :=
  [none, some (.continue 0), some (.continue 3), some (.break 0),
   some (.break 1), some (.break 3), some (.result (.loc 4 5)),
   some (.exception (.loc 4 5)), some (.halt (.word 7)), some .timeOut, some .error]

private def checks : Bool :=
  inputs.map StackSemControl.contLoop == [true, true, false, false, false, false, false, false, false, false, false] &&
  inputs.map (fun result => observe (StackSemControl.exitLoop result)) ==
    [(0,0), (1,0), (1,2), (0,0), (2,0), (2,2), (3,405), (4,405), (5,7), (6,0), (7,0)]

#guard checks

def runChecks : IO Bool := do
  if checks then
    IO.println "PASS exact StackSem loop controls match original HOL branches"
    pure true
  else
    IO.println "FAIL exact StackSem loop controls differ from original HOL branches"
    pure false

end Flapjack.Test.StackSemLoopControlParity
