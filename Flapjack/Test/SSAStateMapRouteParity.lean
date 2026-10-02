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

-- Original sptree intersection observations through the actual cutset caller.
example : (wordSsaRestrict { current := [], next := 17 } [2]).current = [] := by decide +kernel
example : (wordSsaRestrict { current := [(2,7),(0,3)], next := 17 } []).current = [] := by decide +kernel
example : (wordSsaRestrict { current := [(2,7),(2,9),(0,3),(5,11)], next := 17 }
    [2,2,5]).current = [(5,11),(2,7)] := by decide +kernel
example : (wordSsaRestrict { current := [(2,7),(0,3)], next := 17 }
    [99,2]).current = [(2,7)] := by decide +kernel
example : (wordSsaRestrict
    { current := [(6,212),(5,208),(1,204),(0,200),(2,100),(3,101),(4,102)], next := 17 }
    [6,5,1,0,2,3,4]).current =
    [(3,101),(1,204),(5,208),(0,200),(4,102),(2,100),(6,212)] := by decide +kernel
example : (wordSsaRestrict
    { current := [(18446744073709551616,18446744073709551620),(2,7)], next := 18446744073709551620 }
    [18446744073709551616]).current =
    [(18446744073709551616,18446744073709551620)] := by decide +kernel

-- Complete actual reconciliation outputs captured from original HOL.
example : wordSsaReconcileTo (α := Nat)
    { current := [], next := 17 } { current := [], next := 23 }
    [] = .skip := by
  have moves : Compiler.Backend.WordAlloc.ssaReconcileMovesExecutable
      [] [] [] = [] := by decide +kernel
  simp [wordSsaReconcileTo, moves]

example : wordSsaReconcileTo (α := Nat)
    { current := [(2,7)], next := 17 } { current := [(2,7)], next := 23 }
    [2] = .skip := by
  have moves : Compiler.Backend.WordAlloc.ssaReconcileMovesExecutable
      [(2,7)] [(2,7)] [2] = [] := by decide +kernel
  simp [wordSsaReconcileTo, moves]

example : wordSsaReconcileTo (α := Nat)
    { current := [], next := 17 } { current := [(2,7)], next := 23 }
    [2] = .skip := by
  have moves : Compiler.Backend.WordAlloc.ssaReconcileMovesExecutable
      [] [(2,7)] [2] = [] := by decide +kernel
  simp [wordSsaReconcileTo, moves]

example : wordSsaReconcileTo (α := Nat)
    { current := [(2,7)], next := 17 } { current := [], next := 23 }
    [2] = .move 1 [(0,7)] := by
  have moves : Compiler.Backend.WordAlloc.ssaReconcileMovesExecutable
      [(2,7)] [] [2] = [(0,7)] := by decide +kernel
  simp [wordSsaReconcileTo, moves]

example : wordSsaReconcileTo (α := Nat)
    { current := [(2,7),(2,9),(5,11)], next := 17 } { current := [(2,13),(2,17),(5,19)], next := 23 }
    [2,2,5] = .move 1 [(19,11),(13,7)] := by
  have moves : Compiler.Backend.WordAlloc.ssaReconcileMovesExecutable
      [(2,7),(2,9),(5,11)] [(2,13),(2,17),(5,19)] [2,2,5] = [(19,11),(13,7)] := by decide +kernel
  simp [wordSsaReconcileTo, moves]

example : wordSsaReconcileTo (α := Nat)
    { current := [(0,21),(4,41),(6,33),(12,37)], next := 17 } { current := [], next := 23 }
    [0,4,6,12] = .move 1 [(0,21),(0,41),(0,37),(0,33)] := by
  have moves : Compiler.Backend.WordAlloc.ssaReconcileMovesExecutable
      [(0,21),(4,41),(6,33),(12,37)] [] [0,4,6,12] = [(0,21),(0,41),(0,37),(0,33)] := by decide +kernel
  simp [wordSsaReconcileTo, moves]

example : wordSsaReconcileTo (α := Nat)
    { current := [(18446744073709551616,18446744073709551620)], next := 17 } { current := [], next := 23 }
    [18446744073709551616] = .move 1 [(0,18446744073709551620)] := by
  have moves : Compiler.Backend.WordAlloc.ssaReconcileMovesExecutable
      [(18446744073709551616,18446744073709551620)] [] [18446744073709551616] = [(0,18446744073709551620)] := by decide +kernel
  simp [wordSsaReconcileTo, moves]

-- Complete original Move0/map/counter tuples through the production caller.
example : wordSsaListNextVarRenameMove (α := Nat)
    { current := [(2,7),(0,3),(2,9)], next := 999 } 10 [] =
    ({ current := [(0,3),(2,7)], next := 10 }, 10, .move 0 []) := by
  have output : Compiler.Backend.WordAlloc.ssaListNextVarRenameMoveExecutable
      [(2,7),(0,3),(2,9)] 10 [] = ([], [(0,3),(2,7)], 10) := by decide +kernel
  simp [wordSsaListNextVarRenameMove, output]

example : wordSsaListNextVarRenameMove (α := Nat)
    { current := [], next := 999 } 10 [2,5] =
    ({ current := [(5,14),(2,10)], next := 18 }, 18, .move 0 [(10,0),(14,0)]) := by
  have output : Compiler.Backend.WordAlloc.ssaListNextVarRenameMoveExecutable
      [] 10 [2,5] = ([(10,0),(14,0)], [(5,14),(2,10)], 18) := by decide +kernel
  simp [wordSsaListNextVarRenameMove, output]

example : wordSsaListNextVarRenameMove (α := Nat)
    { current := [(2,7),(2,9)], next := 999 } 10 [2,2] =
    ({ current := [(2,14)], next := 18 }, 18, .move 0 [(10,7),(14,7)]) := by
  have output : Compiler.Backend.WordAlloc.ssaListNextVarRenameMoveExecutable
      [(2,7),(2,9)] 10 [2,2] = ([(10,7),(14,7)], [(2,14)], 18) := by decide +kernel
  simp [wordSsaListNextVarRenameMove, output]

example : wordSsaListNextVarRenameMove (α := Nat)
    { current := [(2,10),(5,14)], next := 999 } 10 [2,5,2] =
    ({ current := [(5,14),(2,18)], next := 22 }, 22, .move 0 [(10,10),(14,14),(18,10)]) := by
  have output : Compiler.Backend.WordAlloc.ssaListNextVarRenameMoveExecutable
      [(2,10),(5,14)] 10 [2,5,2] = ([(10,10),(14,14),(18,10)], [(5,14),(2,18)], 22) := by decide +kernel
  simp [wordSsaListNextVarRenameMove, output]

example : wordSsaListNextVarRenameMove (α := Nat)
    { current := [(0,21),(4,41),(6,33),(12,37)], next := 999 } 200 [0,4,12,6] =
    ({ current := [(0,200),(4,204),(12,208),(6,212)], next := 216 }, 216, .move 0 [(200,21),(204,41),(208,37),(212,33)]) := by
  have output : Compiler.Backend.WordAlloc.ssaListNextVarRenameMoveExecutable
      [(0,21),(4,41),(6,33),(12,37)] 200 [0,4,12,6] = ([(200,21),(204,41),(208,37),(212,33)], [(0,200),(4,204),(12,208),(6,212)], 216) := by decide +kernel
  simp [wordSsaListNextVarRenameMove, output]

example : wordSsaListNextVarRenameMove (α := Nat)
    { current := [(18446744073709551616,7)], next := 999 } 18446744073709551616 [18446744073709551616,2] =
    ({ current := [(18446744073709551616,18446744073709551616),(2,18446744073709551620)], next := 18446744073709551624 }, 18446744073709551624, .move 0 [(18446744073709551616,7),(18446744073709551620,0)]) := by
  have output : Compiler.Backend.WordAlloc.ssaListNextVarRenameMoveExecutable
      [(18446744073709551616,7)] 18446744073709551616 [18446744073709551616,2] = ([(18446744073709551616,7),(18446744073709551620,0)], [(18446744073709551616,18446744073709551616),(2,18446744073709551620)], 18446744073709551624) := by decide +kernel
  simp [wordSsaListNextVarRenameMove, output]

end Flapjack.Test.SSAStateMapRouteParity
