import Flapjack.HolRef
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.Leaves
import Flapjack.Misc.Sptree.UnionAlgebra

namespace Flapjack.WordAlloc
open Flapjack.RegAlloc

/-- Flapjack infrastructure for the HOL ShareInst store cases: commute the
singleton through the expression read-set union on the exact unit carrier. -/
private theorem insertReadsStore {width : Nat} [NeZero width]
    (e : WordLangExpHOL (BitVec width)) (v : Nat) (live : NumSet)
    (hw : sptWf live = true) :
    numsetListInsert (v :: getReadsExpHOL e) live =
      sptUnion (getLiveExp e) (sptInsert v () live) := by
  rw [numsetListInsert, insertReadsEqUnion e live hw]
  rw [sptInsert_union, sptUnion_assoc,
    sptUnion_numSet_sym (sptInsert v () .ln) (getLiveExp e),
    ← sptUnion_assoc, sptUnion_insert_ln]

/-- Exact HOL ShareInst Store case, retaining the full original motive. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem clashTreeColouringOk_ShareStore {width : Nat} [NeZero width]
    (v : Nat) (e : WordLangExpHOL (BitVec width)) :
    clashTreeGoal (.shareInst .store v e) := by
  rintro lt f live flive livein flivein ⟨-, hw, -, hd, hi, hc⟩
  simp only [getClashTree, reduceCtorEq, true_or, false_or, if_true] at hc
  exact deltaConcl _ f _ _ live flive livein flivein lt hw hd hi hc
    (fun k => by simp [getWrites, sptDomain])
    (fun hw => by
      simp only [numsetListDelete, getLive, reduceCtorEq, true_or,
        false_or, if_true]
      exact insertReadsStore e v live hw) Iff.rfl

/-- Exact HOL ShareInst Store8 case, retaining the full original motive. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem clashTreeColouringOk_ShareStore8 {width : Nat} [NeZero width]
    (v : Nat) (e : WordLangExpHOL (BitVec width)) :
    clashTreeGoal (.shareInst .store8 v e) := by
  rintro lt f live flive livein flivein ⟨-, hw, -, hd, hi, hc⟩
  simp only [getClashTree, reduceCtorEq, true_or, or_true, false_or, if_true] at hc
  exact deltaConcl _ f _ _ live flive livein flivein lt hw hd hi hc
    (fun k => by simp [getWrites, sptDomain])
    (fun hw => by
      simp only [numsetListDelete, getLive, reduceCtorEq, true_or, or_true,
        false_or, if_true]
      exact insertReadsStore e v live hw) Iff.rfl

/-- Exact HOL ShareInst Store16 case, retaining the full original motive. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem clashTreeColouringOk_ShareStore16 {width : Nat} [NeZero width]
    (v : Nat) (e : WordLangExpHOL (BitVec width)) :
    clashTreeGoal (.shareInst .store16 v e) := by
  rintro lt f live flive livein flivein ⟨-, hw, -, hd, hi, hc⟩
  simp only [getClashTree, reduceCtorEq, true_or, or_true, if_true] at hc
  exact deltaConcl _ f _ _ live flive livein flivein lt hw hd hi hc
    (fun k => by simp [getWrites, sptDomain])
    (fun hw => by
      simp only [numsetListDelete, getLive, reduceCtorEq, true_or, or_true,
        if_true]
      exact insertReadsStore e v live hw) Iff.rfl

/-- Exact HOL ShareInst Store32 case, retaining the full original motive. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem clashTreeColouringOk_ShareStore32 {width : Nat} [NeZero width]
    (v : Nat) (e : WordLangExpHOL (BitVec width)) :
    clashTreeGoal (.shareInst .store32 v e) := by
  rintro lt f live flive livein flivein ⟨-, hw, -, hd, hi, hc⟩
  simp only [getClashTree, reduceCtorEq, or_true, if_true] at hc
  exact deltaConcl _ f _ _ live flive livein flivein lt hw hd hi hc
    (fun k => by simp [getWrites, sptDomain])
    (fun hw => by
      simp only [numsetListDelete, getLive, reduceCtorEq, or_true,
        if_true]
      exact insertReadsStore e v live hw) Iff.rfl

/-- Exact HOL ShareInst Load case, retaining the full original motive. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem clashTreeColouringOk_ShareLoad {width : Nat} [NeZero width]
    (v : Nat) (e : WordLangExpHOL (BitVec width)) :
    clashTreeGoal (.shareInst .load v e) := by
  rintro lt f live flive livein flivein ⟨-, hw, -, hd, hi, hc⟩
  simp only [getClashTree, reduceCtorEq, false_or, if_false] at hc
  exact deltaConcl _ f _ _ live flive livein flivein lt hw hd hi hc
    (fun k => by simpa only [getWrites] using writesSingle v k)
    (fun hw => by
      simp only [numsetListDelete, getLive, reduceCtorEq, false_or, if_false]
      exact insertReadsEqUnion e (sptDelete v live) (sptWfDelete live v hw)) Iff.rfl

/-- Exact HOL ShareInst Load8 case, retaining the full original motive. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem clashTreeColouringOk_ShareLoad8 {width : Nat} [NeZero width]
    (v : Nat) (e : WordLangExpHOL (BitVec width)) :
    clashTreeGoal (.shareInst .load8 v e) := by
  rintro lt f live flive livein flivein ⟨-, hw, -, hd, hi, hc⟩
  simp only [getClashTree, reduceCtorEq, false_or, if_false] at hc
  exact deltaConcl _ f _ _ live flive livein flivein lt hw hd hi hc
    (fun k => by simpa only [getWrites] using writesSingle v k)
    (fun hw => by
      simp only [numsetListDelete, getLive, reduceCtorEq, false_or, if_false]
      exact insertReadsEqUnion e (sptDelete v live) (sptWfDelete live v hw)) Iff.rfl

/-- Exact HOL ShareInst Load16 case, retaining the full original motive. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem clashTreeColouringOk_ShareLoad16 {width : Nat} [NeZero width]
    (v : Nat) (e : WordLangExpHOL (BitVec width)) :
    clashTreeGoal (.shareInst .load16 v e) := by
  rintro lt f live flive livein flivein ⟨-, hw, -, hd, hi, hc⟩
  simp only [getClashTree, reduceCtorEq, false_or, if_false] at hc
  exact deltaConcl _ f _ _ live flive livein flivein lt hw hd hi hc
    (fun k => by simpa only [getWrites] using writesSingle v k)
    (fun hw => by
      simp only [numsetListDelete, getLive, reduceCtorEq, false_or, if_false]
      exact insertReadsEqUnion e (sptDelete v live) (sptWfDelete live v hw)) Iff.rfl

/-- Exact HOL ShareInst Load32 case, retaining the full original motive. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem clashTreeColouringOk_ShareLoad32 {width : Nat} [NeZero width]
    (v : Nat) (e : WordLangExpHOL (BitVec width)) :
    clashTreeGoal (.shareInst .load32 v e) := by
  rintro lt f live flive livein flivein ⟨-, hw, -, hd, hi, hc⟩
  simp only [getClashTree, reduceCtorEq, false_or, if_false] at hc
  exact deltaConcl _ f _ _ live flive livein flivein lt hw hd hi hc
    (fun k => by simpa only [getWrites] using writesSingle v k)
    (fun hw => by
      simp only [numsetListDelete, getLive, reduceCtorEq, false_or, if_false]
      exact insertReadsEqUnion e (sptDelete v live) (sptWfDelete live v hw)) Iff.rfl

end Flapjack.WordAlloc
