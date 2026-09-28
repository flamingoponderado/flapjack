import Flapjack.Pancake.LoopLive.ExactAssignedVars
import Flapjack.Pancake.CrepToLoop.ProgIfExact

/-!
Direct fixtures replaying `loop_props_assigned_vars_probe.out` rows
`avs_seq_split`, `avs_nested_seq_split_two`, and positive/negative
`avs_nested_assign`, plus `crep_to_loop_assigned_vars_mapidx_probe.out` rows
`avma_two`/`avma_two_negative` and `prog_if_probe.out`'s positive rendered
program / `prog_if_wrong_result=F`.
-/

namespace Flapjack.Test.LoopExactAssignedVarsParity

open Flapjack

private def wvar (name : Nat) : HolLoopExp 64 := .var name

def seqSplitPositive : Bool :=
  decide (holLoopAssignedVars
    (.seq (.assign 1 (wvar 0)) (.assign 2 (wvar 1))) = [1, 2])

def seqSplitNegative : Bool :=
  decide (holLoopAssignedVars
    (.seq (.assign 1 (wvar 0)) (.assign 2 (wvar 1))) = [1])

def nestedSeqSplitPositive : Bool :=
  decide (holLoopAssignedVars
    (holLoopNestedSeq
      (([.assign 1 (wvar 0), .assign 2 (wvar 1)] : List (HolLoopProg 64)) ++
        [.assign 3 (wvar 2)])) = [1, 2, 3])

def nestedSeqSplitNegative : Bool :=
  decide (holLoopAssignedVars
    (holLoopNestedSeq
      (([.assign 1 (wvar 0), .assign 2 (wvar 1)] : List (HolLoopProg 64)) ++
        [.assign 3 (wvar 2)])) = [1, 2, 8])

def nestedAssignPositive : Bool :=
  decide (holLoopAssignedVars
    (holLoopNestedSeq
      (List.zipWith HolLoopProg.assign [3, 4, 5]
        [wvar 0, wvar 1, wvar 2])) = [3, 4, 5])

def nestedAssignNegative : Bool :=
  decide (holLoopAssignedVars
    (holLoopNestedSeq
      (List.zipWith HolLoopProg.assign [3, 4, 5]
        [wvar 0, wvar 1, wvar 2])) = [3, 4, 8])

def mapIdxAssignPositive : Bool :=
  decide (holLoopAssignedVars
    (holLoopNestedSeq
      (([wvar 0, wvar 1] : List (HolLoopExp 64)).mapIdx
        (fun index expression => .assign (index + 3) expression))) = [3, 4])

def mapIdxAssignNegative : Bool :=
  decide (holLoopAssignedVars
    (holLoopNestedSeq
      (([wvar 0, wvar 1] : List (HolLoopExp 64)).mapIdx
        (fun index expression => .assign (index + 3) expression))) = [3, 5])

private def progIfInput : List (HolLoopProg 8) :=
  progIfExact .notEqual [.skip] [.tick] (.const 2) (.const 3) 3 4
    (sptInsert 1 () (sptInsert 2 () Spt.ln))

private def progIfExpected : List (HolLoopProg 8) :=
  [.skip, .tick,
   .assign 3 (.const 2),
   .assign 4 (.const 3),
   .ite .notEqual 3 (.reg 4)
     (.assign 3 (.const 1))
     (.assign 3 (.const 0))
     (sptListInsert [3, 4] (sptInsert 1 () (sptInsert 2 () Spt.ln)))]

theorem progIfPositive : progIfInput = progIfExpected := rfl

theorem progIfNegative : progIfInput ≠ [.skip] := by
  simp [progIfInput, progIfExact]

#guard seqSplitPositive
#guard !seqSplitNegative
#guard nestedSeqSplitPositive
#guard !nestedSeqSplitNegative
#guard nestedAssignPositive
#guard !nestedAssignNegative
#guard mapIdxAssignPositive
#guard !mapIdxAssignNegative

end Flapjack.Test.LoopExactAssignedVarsParity
