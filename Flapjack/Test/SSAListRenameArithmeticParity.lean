import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASetup.ListNextVarRenameArithmetic

namespace Flapjack.Test.SSAListRenameArithmetic
open Flapjack Flapjack.Compiler.Backend.WordAlloc

private def observe (names : List Nat) (ssa : Spt Nat) (next : Nat) :
    List Nat × List (Option Nat) × Nat × Bool × Bool × Bool :=
  let (renamed, ssaOut, nextOut) := listNextVarRename names ssa next
  (renamed, [0,1,2,4,9,100,1208925819614629174706176].map (fun k => sptLookup k ssaOut),
    nextOut, decide renamed.Nodup,
    decide (renamed = (List.range names.length).map (fun x => 4 * x + next)),
    decide (nextOut = next + 4 * names.length))

example : observe [] (sptFromAList [(9,99)]) 5 =
    ([], [none, none, none, none, some 99, none, none], 5, true, true, true) := by decide +kernel

example : let result := listNextVarRename [] (sptFromAList [(9,99)]) 5
    result.1.Nodup ∧
    result.1 = (List.range ([] : List Nat).length).map (fun x => 4 * x + 5) ∧
    result.2.2 = 5 + 4 * ([] : List Nat).length :=
  listNextVarRenameLemma1 [] (sptFromAList [(9,99)]) 5 _ _ _ rfl

example : observe [1, 2, 1] (sptFromAList [(9,99),(1,88)]) 5 =
    ([5, 9, 13], [none, some 13, some 9, none, some 99, none, none], 17, true, true, true) := by decide +kernel

example : let result := listNextVarRename [1, 2, 1] (sptFromAList [(9,99),(1,88)]) 5
    result.1.Nodup ∧
    result.1 = (List.range ([1, 2, 1] : List Nat).length).map (fun x => 4 * x + 5) ∧
    result.2.2 = 5 + 4 * ([1, 2, 1] : List Nat).length :=
  listNextVarRenameLemma1 [1, 2, 1] (sptFromAList [(9,99),(1,88)]) 5 _ _ _ rfl

example : observe [0, 4] (.bn .ln .ln) 0 =
    ([0, 4], [some 0, none, none, some 4, none, none, none], 8, true, true, true) := by decide +kernel

example : let result := listNextVarRename [0, 4] (.bn .ln .ln) 0
    result.1.Nodup ∧
    result.1 = (List.range ([0, 4] : List Nat).length).map (fun x => 4 * x + 0) ∧
    result.2.2 = 0 + 4 * ([0, 4] : List Nat).length :=
  listNextVarRenameLemma1 [0, 4] (.bn .ln .ln) 0 _ _ _ rfl

example : observe [9] (sptFromAList [(9,99),(1,88)]) 101 =
    ([101], [none, some 88, none, none, some 101, none, none], 105, true, true, true) := by decide +kernel

example : let result := listNextVarRename [9] (sptFromAList [(9,99),(1,88)]) 101
    result.1.Nodup ∧
    result.1 = (List.range ([9] : List Nat).length).map (fun x => 4 * x + 101) ∧
    result.2.2 = 101 + 4 * ([9] : List Nat).length :=
  listNextVarRenameLemma1 [9] (sptFromAList [(9,99),(1,88)]) 101 _ _ _ rfl

example : observe [2, 2, 2] (.ln) 0 =
    ([0, 4, 8], [none, none, some 8, none, none, none, none], 12, true, true, true) := by decide +kernel

example : let result := listNextVarRename [2, 2, 2] (.ln) 0
    result.1.Nodup ∧
    result.1 = (List.range ([2, 2, 2] : List Nat).length).map (fun x => 4 * x + 0) ∧
    result.2.2 = 0 + 4 * ([2, 2, 2] : List Nat).length :=
  listNextVarRenameLemma1 [2, 2, 2] (.ln) 0 _ _ _ rfl

example : observe [100, 0, 4] (.ln) 3 =
    ([3, 7, 11], [some 7, none, none, some 11, none, some 3, none], 15, true, true, true) := by decide +kernel

example : let result := listNextVarRename [100, 0, 4] (.ln) 3
    result.1.Nodup ∧
    result.1 = (List.range ([100, 0, 4] : List Nat).length).map (fun x => 4 * x + 3) ∧
    result.2.2 = 3 + 4 * ([100, 0, 4] : List Nat).length :=
  listNextVarRenameLemma1 [100, 0, 4] (.ln) 3 _ _ _ rfl

example : observe [1208925819614629174706176, 1208925819614629174706176] (.ln) 1208925819614629174706176 =
    ([1208925819614629174706176, 1208925819614629174706180], [none, none, none, none, none, none, some 1208925819614629174706180], 1208925819614629174706184, true, true, true) := by decide +kernel

example : let result := listNextVarRename [1208925819614629174706176, 1208925819614629174706176] (.ln) 1208925819614629174706176
    result.1.Nodup ∧
    result.1 = (List.range ([1208925819614629174706176, 1208925819614629174706176] : List Nat).length).map (fun x => 4 * x + 1208925819614629174706176) ∧
    result.2.2 = 1208925819614629174706176 + 4 * ([1208925819614629174706176, 1208925819614629174706176] : List Nat).length :=
  listNextVarRenameLemma1 [1208925819614629174706176, 1208925819614629174706176] (.ln) 1208925819614629174706176 _ _ _ rfl

example : observe [0, 1, 2, 3, 4, 5] (.ln) 2 =
    ([2, 6, 10, 14, 18, 22], [some 2, some 6, some 10, some 18, none, none, none], 26, true, true, true) := by decide +kernel

example : let result := listNextVarRename [0, 1, 2, 3, 4, 5] (.ln) 2
    result.1.Nodup ∧
    result.1 = (List.range ([0, 1, 2, 3, 4, 5] : List Nat).length).map (fun x => 4 * x + 2) ∧
    result.2.2 = 2 + 4 * ([0, 1, 2, 3, 4, 5] : List Nat).length :=
  listNextVarRenameLemma1 [0, 1, 2, 3, 4, 5] (.ln) 2 _ _ _ rfl

example (names : List Nat) (ssa : Spt Nat) (next : Nat)
    (renamed : List Nat) (ssaOut : Spt Nat) (nextOut : Nat)
    (rename : listNextVarRename names ssa next = (renamed, ssaOut, nextOut)) :
    renamed.Nodup ∧
    renamed = (List.range names.length).map (fun x => 4 * x + next) ∧
    nextOut = next + 4 * names.length :=
  listNextVarRenameLemma1 names ssa next renamed ssaOut nextOut rename

end Flapjack.Test.SSAListRenameArithmetic
