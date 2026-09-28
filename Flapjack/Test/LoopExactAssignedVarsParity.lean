import Flapjack.Pancake.LoopLang.AssignedVars
import Flapjack.Pancake.Semantics.LoopProps.AssignedVars
import Flapjack.Pancake.CrepToLoop.Proofs.AssignedVars

/-!
Direct fixtures replaying `loop_props_assigned_vars_probe.out` rows
`avs_seq_split`, `avs_nested_seq_split_two`, and positive/negative
`avs_nested_assign`, plus `crep_to_loop_assigned_vars_mapidx_probe.out` rows
`avma_two`/`avma_two_negative`.
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
    (loopNestedSeqHOL
      (([.assign 1 (wvar 0), .assign 2 (wvar 1)] : List (HolLoopProg 64)) ++
        [.assign 3 (wvar 2)])) = [1, 2, 3])

def nestedSeqSplitNegative : Bool :=
  decide (holLoopAssignedVars
    (loopNestedSeqHOL
      (([.assign 1 (wvar 0), .assign 2 (wvar 1)] : List (HolLoopProg 64)) ++
        [.assign 3 (wvar 2)])) = [1, 2, 8])

def nestedAssignPositive : Bool :=
  decide (holLoopAssignedVars
    (loopNestedSeqHOL
      (List.zipWith HolLoopProg.assign [3, 4, 5]
        [wvar 0, wvar 1, wvar 2])) = [3, 4, 5])

def nestedAssignNegative : Bool :=
  decide (holLoopAssignedVars
    (loopNestedSeqHOL
      (List.zipWith HolLoopProg.assign [3, 4, 5]
        [wvar 0, wvar 1, wvar 2])) = [3, 4, 8])

def mapIdxAssignPositive : Bool :=
  decide (holLoopAssignedVars
    (loopNestedSeqHOL
      (([wvar 0, wvar 1] : List (HolLoopExp 64)).mapIdx
        (fun index expression => .assign (index + 3) expression))) = [3, 4])

def mapIdxAssignNegative : Bool :=
  decide (holLoopAssignedVars
    (loopNestedSeqHOL
      (([wvar 0, wvar 1] : List (HolLoopExp 64)).mapIdx
        (fun index expression => .assign (index + 3) expression))) = [3, 5])

#guard seqSplitPositive
#guard !seqSplitNegative
#guard nestedSeqSplitPositive
#guard !nestedSeqSplitNegative
#guard nestedAssignPositive
#guard !nestedAssignNegative
#guard mapIdxAssignPositive
#guard !mapIdxAssignNegative

end Flapjack.Test.LoopExactAssignedVarsParity
