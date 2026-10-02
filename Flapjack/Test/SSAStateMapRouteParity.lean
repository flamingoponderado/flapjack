import Flapjack.Compiler.Backend.WordAlloc.ProductionSSAStateRoute

/-! Exact original HOL EVAL rows from `ssa_state_map_route_probe.out`.
These check the executed allocator callers, including the complete decoded
map order and counters. Regression observations are not equivalence proofs. -/
namespace Flapjack.Test.SSAStateMapRouteParity
open Flapjack Flapjack.Compiler.Backend.WordAlloc

theorem freshEmpty : wordSsaFresh {current := [],next := 1} 0 =
    ({current := [(0,1)],next := 5},1) := by decide +kernel

theorem freshDuplicate : wordSsaFresh {current := [(2,7),(2,9),(0,3)],next := 10} 5 =
    ({current := [(5,10),(0,3),(2,7)],next := 14},10) := by decide +kernel

theorem freshOverwrite : wordSsaFresh {current := [(2,7),(2,9),(0,3)],next := 10} 2 =
    ({current := [(0,3),(2,10)],next := 14},10) := by decide +kernel

theorem freshBig : wordSsaFresh {current := [(2,7)],next := 18446744073709551616}
      18446744073709551616 =
    ({current := [(18446744073709551616,18446744073709551616),(2,7)],
      next := 18446744073709551620},18446744073709551616) := by decide +kernel

theorem forceEmpty : wordSsaForceRename [] {current := [(2,7),(0,3),(2,9)],next := 19} =
    {current := [(0,3),(2,7)],next := 19} := by decide +kernel

theorem forceDuplicate : wordSsaForceRename [(2,11),(2,13),(1,17)]
      {current := [(2,7),(2,9),(0,3)],next := 19} =
    {current := [(1,17),(0,3),(2,13)],next := 19} := by decide +kernel

theorem forceLinearRegisters : wordSsaForceRename [(0,200),(1,204),(5,208),(6,212)]
      {current := [(2,100),(3,101),(4,102)],next := 216} =
    {current := [(3,101),(1,204),(5,208),(0,200),(4,102),(2,100),(6,212)],next := 216} := by
  decide +kernel

theorem keysOrder : wordSsaKeys
      {current := [(6,212),(5,208),(1,204),(0,200),(2,100),(3,101),(4,102)],next := 216} =
    [3,1,5,0,4,2,6] := by decide +kernel

end Flapjack.Test.SSAStateMapRouteParity
