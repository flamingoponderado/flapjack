import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.LoopCases

namespace Flapjack.Test.WordAllocLoopCheckerParity
open Flapjack Flapjack.WordAlloc Flapjack.RegAlloc

/-! Same-input kernel replay of seven freshly evaluated original HOL checker
rows. These finite observations supplement the universal case proofs; they
are not cross-prover equivalence or whole allocator correctness. -/
private def n : NumSet := sptInsert 1 () .ln
private def e : NumSet := sptInsert 2 () .ln
-- lc_break_absent=T
example : checkClashTree id (getClashTree (.break 2 : WordLangProgHOL (BitVec 64)) [])
    .ln .ln = some (.ln, .ln) := by
  simp only [getClashTree, checkClashTree]
  decide +kernel
-- lc_continue_absent=T
example : checkClashTree id (getClashTree (.continue 2 : WordLangProgHOL (BitVec 64)) [])
    .ln .ln = some (.ln, .ln) := by
  simp only [getClashTree, checkClashTree]
  decide +kernel
-- lc_break_present=T
example : checkClashTree id (getClashTree (.break 0 : WordLangProgHOL (BitVec 64)) [(n,e)])
    .ln .ln = some (e,e) := by
  simp only [getClashTree, checkClashTree]
  decide +kernel
-- lc_continue_present=T
example : checkClashTree id (getClashTree (.continue 0 : WordLangProgHOL (BitVec 64)) [(n,e)])
    .ln .ln = some (n,n) := by
  simp only [getClashTree, checkClashTree]
  decide +kernel
-- lc_loop_skip=T
example : checkClashTree id (getClashTree (.loop n .skip e : WordLangProgHOL (BitVec 64)) [])
    .ln .ln = some (n,n) := by
  simp only [getClashTree, checkClashTree]
  decide +kernel
-- lc_loop_continue=T
example : checkClashTree id (getClashTree (.loop n (.continue 0) e : WordLangProgHOL (BitVec 64)) [])
    .ln .ln = some (n,n) := by
  simp only [getClashTree, checkClashTree]
  decide +kernel
-- lc_break_collision=T
example : checkClashTree (fun _ => 0)
    (getClashTree (.break 0 : WordLangProgHOL (BitVec 64)) [(.ln,sptInsert 1 () e)])
    .ln .ln = none := by
  simp only [getClashTree, checkClashTree]
  decide +kernel

example : clashTreeGoal (.break 0 : WordLangProgHOL (BitVec 64)) := clashTreeColouringOk_Break 0
example : clashTreeGoal (.continue 0 : WordLangProgHOL (BitVec 64)) := clashTreeColouringOk_Continue 0
end Flapjack.Test.WordAllocLoopCheckerParity
