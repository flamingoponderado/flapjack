import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.CallNone

namespace Flapjack.Test.ClashTreeCallNoneParity
open Flapjack Flapjack.WordAlloc Flapjack.RegAlloc
-- ccn_empty=T
example : checkClashTree (id) (getClashTree (.call none (none) [] (none) : WordLangProgHOL (BitVec 8)) []) .ln .ln = some (numsetListInsert [] .ln,numsetListInsert [] .ln) := by
  simp [getClashTree, checkClashTree, checkCol, numsetListInsert, sptToAList, sptFoldi, sptFromAList]
-- ccn_one=T
example : checkClashTree (id) (getClashTree (.call none (some 10) [0] (none) : WordLangProgHOL (BitVec 8)) []) .ln .ln = some (numsetListInsert [0] .ln,numsetListInsert [0] .ln) := by
  simp [getClashTree, checkClashTree, checkCol, numsetListInsert, sptToAList, sptFoldi, sptFromAList]
-- ccn_duplicate=T
example : checkClashTree (id) (getClashTree (.call none (none) [0,0] (none) : WordLangProgHOL (BitVec 8)) []) .ln .ln = some (numsetListInsert [0,0] .ln,numsetListInsert [0,0] .ln) := by
  simp [getClashTree, checkClashTree, checkCol, numsetListInsert, sptToAList, sptFoldi, sptInsert, sptFromAList]
-- ccn_args=T
example : checkClashTree (id) (getClashTree (.call none (some 10) [0,1] (none) : WordLangProgHOL (BitVec 8)) []) .ln .ln = some (numsetListInsert [0,1] .ln,numsetListInsert [0,1] .ln) := by
  simp [getClashTree, checkClashTree, checkCol, numsetListInsert, sptToAList, sptFoldi, sptInsert, sptFromAList, lrNext]
-- ccn_collision=F
example : checkClashTree (fun _ => 0) (getClashTree (.call none (none) [0,1] (none) : WordLangProgHOL (BitVec 8)) []) .ln .ln ≠ some (numsetListInsert [0,1] .ln,numsetListInsert [0,1] .ln) := by
  simp [getClashTree, checkClashTree, checkCol, numsetListInsert, sptToAList, sptFoldi, sptInsert, lrNext]
-- ccn_handler_ignored=T
example : checkClashTree (id) (getClashTree (.call none (some 10) [0] (some (7,.skip,8,9)) : WordLangProgHOL (BitVec 8)) []) .ln .ln = some (numsetListInsert [0] .ln,numsetListInsert [0] .ln) := by
  simp [getClashTree, checkClashTree, checkCol, numsetListInsert, sptToAList, sptFoldi, sptFromAList]

example {width : Nat} [NeZero width] (target : Option Nat) (args : List Nat) (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) : clashTreeGoal (.call none target args handler : WordLangProgHOL (BitVec width)) := clashTreeColouringOk_CallNone target args handler

end Flapjack.Test.ClashTreeCallNoneParity
