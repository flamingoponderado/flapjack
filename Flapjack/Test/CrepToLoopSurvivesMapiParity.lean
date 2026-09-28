import Flapjack.Pancake.CrepToLoop.Proofs.AssignedVars

/-!
Direct Lean replay of the original HOL EVAL rows in
`scripts/hol-probes/crep_to_loop_survives_mapi_probe.out` for
`survives_MAPi_Assign`
(`cakeml/pancake/proofs/crep_to_loopProofScript.sml:368-379`), using the exact
width-indexed `HolLoopProg 8` carrier and the exact tagged `survivesHOLExact`.
-/

namespace Flapjack.Test.CrepToLoopSurvivesMapiParity

open Flapjack

private def lesOne : List (HolLoopExp 8) := [.const (5 : BitVec 8)]

private def lesTwo : List (HolLoopExp 8) := [.const (5 : BitVec 8), .var 7]

private def lesThree : List (HolLoopExp 8) :=
  [.var 9, .const (0 : BitVec 8), .var 9]

private def mapiAssign (les : List (HolLoopExp 8)) (offset : Nat) :
    HolLoopProg 8 :=
  holLoopNestedSeq
    (les.mapIdx (fun index expression => HolLoopProg.assign (index + offset) expression))

-- Rows `survives_mapi_empty`, `survives_mapi_one`, `survives_mapi_two`,
-- `survives_mapi_three` of the direct original-HOL probe.
#guard survivesHOLExact (width := 8) 0 (mapiAssign [] 0) = true
#guard survivesHOLExact (width := 8) 1 (mapiAssign lesOne 3) = true
#guard survivesHOLExact (width := 8) 2 (mapiAssign lesTwo 1) = true
#guard survivesHOLExact (width := 8) 9 (mapiAssign lesThree 4) = true

-- Kernel-checked replay through the exact tagged theorem itself.
example : survivesHOLExact (width := 8) 0 (mapiAssign [] 0) = true :=
  holSurvivesMapiAssign 0 [] 0

example : survivesHOLExact (width := 8) 1 (mapiAssign lesOne 3) = true :=
  holSurvivesMapiAssign 1 lesOne 3

example : survivesHOLExact (width := 8) 2 (mapiAssign lesTwo 1) = true :=
  holSurvivesMapiAssign 2 lesTwo 1

example : survivesHOLExact (width := 8) 9 (mapiAssign lesThree 4) = true :=
  holSurvivesMapiAssign 9 lesThree 4

def runChecks : IO Bool := do
  let ok :=
    survivesHOLExact (width := 8) 0 (mapiAssign [] 0) &&
    survivesHOLExact (width := 8) 1 (mapiAssign lesOne 3) &&
    survivesHOLExact (width := 8) 2 (mapiAssign lesTwo 1) &&
    survivesHOLExact (width := 8) 9 (mapiAssign lesThree 4)
  if ok then
    IO.println "PASS crep_to_loop survives_MAPi_Assign exact HOL rows"
  else
    IO.println "FAIL crep_to_loop survives_MAPi_Assign exact HOL rows"
  pure ok

end Flapjack.Test.CrepToLoopSurvivesMapiParity