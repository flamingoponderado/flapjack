import Flapjack.Pancake.CrepToLoop.Proofs.SurvivesMapiAssign

namespace Flapjack.Test

open Flapjack

/-! Direct HOL-EVAL rows are in
    `scripts/hol-probes/crep_to_loop_survives_mapi_assign_probe.out`. -/

theorem survivesMapiAssignNilHOLFixture :
    survivesHOLExact 4
      (holLoopNestedSeq
        (([] : List (HolLoopExp 64)).mapIdx (fun index expression =>
          HolLoopProg.assign (index + 3) expression))) = true :=
  holSurvivesMapiAssign 4 [] 3

theorem survivesMapiAssignOneHOLFixture :
    survivesHOLExact 9
      (holLoopNestedSeq
        (([HolLoopExp.var 0] : List (HolLoopExp 64)).mapIdx
          (fun index expression => HolLoopProg.assign (index + 5) expression))) = true :=
  holSurvivesMapiAssign 9 [HolLoopExp.var 0] 5

theorem survivesMapiAssignThreeHOLFixture :
    survivesHOLExact 17
      (holLoopNestedSeq
        (([HolLoopExp.var 0, .var 1, .var 2] : List (HolLoopExp 64)).mapIdx
          (fun index expression => HolLoopProg.assign (index + 7) expression))) = true :=
  holSurvivesMapiAssign 17 [HolLoopExp.var 0, .var 1, .var 2] 7

theorem survivesMapiAssignZeroOffsetHOLFixture :
    survivesHOLExact 0
      (holLoopNestedSeq
        (([HolLoopExp.var 0, .var 1] : List (HolLoopExp 64)).mapIdx
          (fun index expression => HolLoopProg.assign (index + 0) expression))) = true :=
  holSurvivesMapiAssign 0 [HolLoopExp.var 0, .var 1] 0

end Flapjack.Test
