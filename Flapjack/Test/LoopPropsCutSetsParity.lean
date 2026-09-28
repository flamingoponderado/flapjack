import Flapjack.Pancake.Semantics.LoopProps.CutSets

namespace Flapjack.Test

open Flapjack

private def cutSetsSeed : NumSet := sptInsert 8 () .ln

private def cutSetsLive : NumSet := sptInsert 9 () .ln

-- Direct HOL EVAL rows are in scripts/hol-probes/loop_props_cut_sets_probe.out.
example : cutSetsHOL (width := 8) cutSetsSeed (.skip : HolLoopProg 8) =
    cutSetsSeed := rfl

example : cutSetsHOL (width := 8) cutSetsSeed (.locValue 3 4 : HolLoopProg 8) =
    sptInsert 3 () cutSetsSeed := rfl

example : cutSetsHOL (width := 8) cutSetsSeed
    (.assign 4 (.const 0) : HolLoopProg 8) = sptInsert 4 () cutSetsSeed := rfl

example : cutSetsHOL (width := 8) cutSetsSeed (.load32 5 6 : HolLoopProg 8) =
    sptInsert 6 () cutSetsSeed := rfl

example : cutSetsHOL (width := 8) cutSetsSeed (.loadByte 7 9 : HolLoopProg 8) =
    sptInsert 9 () cutSetsSeed := rfl

example : cutSetsHOL (width := 8) cutSetsSeed
    (.seq (.locValue 1 2) (.assign 2 (.const 0)) : HolLoopProg 8) =
    sptInsert 2 () (sptInsert 1 () cutSetsSeed) := rfl

example : cutSetsHOL (width := 8) cutSetsSeed
    (.ite .equal 1 (.reg 2) .skip .tick cutSetsLive : HolLoopProg 8) =
    cutSetsLive := rfl

example : cutSetsHOL (width := 8) cutSetsSeed
    (.arith (.longDiv 1 2 3 4 5) : HolLoopProg 8) =
    sptInsert 1 () (sptInsert 2 () cutSetsSeed) := rfl

example : cutSetsHOL (width := 8) cutSetsSeed
    (.arith (.longMul 3 4 5 6) : HolLoopProg 8) =
    sptInsert 3 () (sptInsert 4 () cutSetsSeed) := rfl

example : cutSetsHOL (width := 8) cutSetsSeed
    (.arith (.div 7 8 9) : HolLoopProg 8) = sptInsert 7 () cutSetsSeed := rfl

example : cutSetsHOL (width := 8) cutSetsSeed (.break 11 : HolLoopProg 8) =
    cutSetsSeed := rfl

end Flapjack.Test
