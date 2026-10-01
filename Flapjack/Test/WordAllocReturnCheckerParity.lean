import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.ReturnNoHandler
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.Leaves
namespace Flapjack.Test.WordAllocReturnCheckerParity
open Flapjack Flapjack.WordAlloc Flapjack.RegAlloc
/-! Same-input kernel replay of original returning Call checker equations.
Includes both return-set and argument-set collisions. Finite regression only. -/
-- rc_empty=T
example : let p : WordLangProgHOL (BitVec 64) := .call (some ([],(.ln,.ln),.skip,7,8)) (none) [] none;
  checkClashTree (id) (getClashTree p []) .ln .ln = some (getLive p .ln [], getLive p .ln []) := by
  dsimp only
  simp only [getClashTree, checkClashTree]
  decide +kernel

-- rc_cuts=T
example : let p : WordLangProgHOL (BitVec 64) := .call (some ([5],(sptInsert 1 () .ln,sptInsert 2 () .ln),.skip,7,8)) (some 99) [3,4] none;
  checkClashTree (id) (getClashTree p []) .ln .ln = some (getLive p .ln [], getLive p .ln []) := by
  dsimp only
  simp only [getClashTree, checkClashTree]
  decide +kernel

-- rc_duplicate_args=T
example : let p : WordLangProgHOL (BitVec 64) := .call (some ([5,5],(sptInsert 1 () .ln,sptInsert 2 () .ln),.skip,7,8)) (none) [3,3,4] none;
  checkClashTree (id) (getClashTree p []) .ln .ln = some (getLive p .ln [], getLive p .ln []) := by
  dsimp only
  simp only [getClashTree, checkClashTree]
  decide +kernel

-- rc_return_tick=T
example : let p : WordLangProgHOL (BitVec 64) := .call (some ([5],(.ln,.ln),.tick,7,8)) (some 0) [3] none;
  checkClashTree (id) (getClashTree p []) .ln .ln = some (getLive p .ln [], getLive p .ln []) := by
  dsimp only
  simp only [getClashTree, checkClashTree]
  decide +kernel

-- rc_return_break=T
example : let p : WordLangProgHOL (BitVec 64) := .call (some ([5],(.ln,.ln),.break 0,7,8)) (none) [3] none;
  checkClashTree (id) (getClashTree p [(sptInsert 8 () .ln,sptInsert 9 () .ln)]) .ln .ln = some (getLive p .ln [(sptInsert 8 () .ln,sptInsert 9 () .ln)], getLive p .ln [(sptInsert 8 () .ln,sptInsert 9 () .ln)]) := by
  dsimp only
  simp only [getClashTree, checkClashTree]
  decide +kernel

-- rc_return_collision=T
example : let p : WordLangProgHOL (BitVec 64) := .call (some ([5,6],(.ln,.ln),.skip,7,8)) (none) [] none;
  checkClashTree (fun _ => 0) (getClashTree p []) .ln .ln = none := by
  dsimp only
  simp only [getClashTree, checkClashTree]
  decide +kernel

-- rc_args_collision=T
example : let p : WordLangProgHOL (BitVec 64) := .call (some ([],(.ln,.ln),.skip,7,8)) (none) [3,4] none;
  checkClashTree (fun _ => 0) (getClashTree p []) .ln .ln = none := by
  dsimp only
  simp only [getClashTree, checkClashTree]
  decide +kernel

example : clashTreeGoal (.call (some ([],(.ln,.ln),.skip,7,8)) none [] none :
    WordLangProgHOL (BitVec 64)) :=
  clashTreeColouringOk_ReturnNoHandler [] (.ln,.ln) .skip 7 8 none [] clashTreeColouringOk_Skip
end Flapjack.Test.WordAllocReturnCheckerParity
