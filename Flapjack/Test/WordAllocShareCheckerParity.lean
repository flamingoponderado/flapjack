import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.ShareInst
namespace Flapjack.Test.WordAllocShareCheckerParity
open Flapjack Flapjack.WordAlloc Flapjack.RegAlloc
/-! Same-input kernel replay of eight fresh original HOL checker equations.
The universal case theorems retain the complete original motive. -/
-- sc_store=T
example : checkClashTree id
    (getClashTree (.shareInst .store 5 (.var 2) : WordLangProgHOL (BitVec 64)) [])
    .ln .ln = some (sptInsert 5 () (sptInsert 2 () .ln), sptInsert 5 () (sptInsert 2 () .ln)) := by
  simp only [getClashTree, checkClashTree, reduceCtorEq, true_or,
    false_or, if_true]
  decide +kernel

-- sc_store8=T
example : checkClashTree id
    (getClashTree (.shareInst .store8 5 (.var 2) : WordLangProgHOL (BitVec 64)) [])
    .ln .ln = some (sptInsert 5 () (sptInsert 2 () .ln), sptInsert 5 () (sptInsert 2 () .ln)) := by
  simp only [getClashTree, checkClashTree, reduceCtorEq, true_or, or_true,
    false_or, if_true]
  decide +kernel

-- sc_store16=T
example : checkClashTree id
    (getClashTree (.shareInst .store16 5 (.var 2) : WordLangProgHOL (BitVec 64)) [])
    .ln .ln = some (sptInsert 5 () (sptInsert 2 () .ln), sptInsert 5 () (sptInsert 2 () .ln)) := by
  simp only [getClashTree, checkClashTree, reduceCtorEq, true_or, or_true,
    if_true]
  decide +kernel

-- sc_store32=T
example : checkClashTree id
    (getClashTree (.shareInst .store32 5 (.var 2) : WordLangProgHOL (BitVec 64)) [])
    .ln .ln = some (sptInsert 5 () (sptInsert 2 () .ln), sptInsert 5 () (sptInsert 2 () .ln)) := by
  simp only [getClashTree, checkClashTree, reduceCtorEq, or_true,
    if_true]
  decide +kernel

-- sc_load=T
example : checkClashTree id
    (getClashTree (.shareInst .load 5 (.var 2) : WordLangProgHOL (BitVec 64)) [])
    .ln .ln = some (sptInsert 2 () .ln, sptInsert 2 () .ln) := by
  simp only [getClashTree, checkClashTree, reduceCtorEq,
    false_or, if_false]
  decide +kernel

-- sc_load8=T
example : checkClashTree id
    (getClashTree (.shareInst .load8 5 (.var 2) : WordLangProgHOL (BitVec 64)) [])
    .ln .ln = some (sptInsert 2 () .ln, sptInsert 2 () .ln) := by
  simp only [getClashTree, checkClashTree, reduceCtorEq,
    false_or, if_false]
  decide +kernel

-- sc_load16=T
example : checkClashTree id
    (getClashTree (.shareInst .load16 5 (.var 2) : WordLangProgHOL (BitVec 64)) [])
    .ln .ln = some (sptInsert 2 () .ln, sptInsert 2 () .ln) := by
  simp only [getClashTree, checkClashTree, reduceCtorEq,
    false_or, if_false]
  decide +kernel

-- sc_load32=T
example : checkClashTree id
    (getClashTree (.shareInst .load32 5 (.var 2) : WordLangProgHOL (BitVec 64)) [])
    .ln .ln = some (sptInsert 2 () .ln, sptInsert 2 () .ln) := by
  simp only [getClashTree, checkClashTree, reduceCtorEq,
    false_or, if_false]
  decide +kernel

end Flapjack.Test.WordAllocShareCheckerParity
