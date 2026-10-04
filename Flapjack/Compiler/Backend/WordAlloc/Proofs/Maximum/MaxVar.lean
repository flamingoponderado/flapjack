import Flapjack.Pancake.WordLang.MaxVar
import Flapjack.Pancake.WordConvs.ProgramMonotonicity
import Flapjack.Compiler.Backend.WordAlloc.Proofs.MaxVarExp
import Flapjack.Compiler.Backend.WordAlloc.Proofs.MaxVarInst
import Flapjack.Compiler.Backend.WordAlloc.Proofs.Maximum.Max3

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack induction infrastructure, with no independent HOL declaration:
a bound on the literal list maximum bounds all listed registers. -/
private theorem listBound (values : List Nat) (bound : Nat)
    (maximum : maxList values ≤ bound) :
    values.all (fun x => decide (x ≤ bound)) = true := by
  apply List.all_eq_true.mpr
  intro x member
  simp only [decide_eq_true_eq]
  exact Nat.le_trans (maxList_ge_of_mem values x member) maximum

/-- Flapjack induction infrastructure lifting the accepted expression theorem
through the accepted monotonicity port, without an extra public premise. -/
private theorem expressionBound {width : Nat} [NeZero width]
    (expression : WordLangExpHOL (BitVec width)) (bound : Nat)
    (maximum : maxVarExpHOL expression ≤ bound) :
    everyVarExpHOL (fun x => decide (x ≤ bound)) expression = true := by
  apply everyVarExpMono _ expression (fun x => decide (x ≤ bound))
  refine ⟨?_, maxVarExpMax expression⟩
  intro x bounded
  simp only [decide_eq_true_eq] at bounded ⊢
  exact Nat.le_trans bounded maximum

/-- Flapjack induction infrastructure lifting the accepted instruction theorem
through the accepted monotonicity port, preserving width-dependent clauses. -/
private theorem instructionBound {width : Nat} [NeZero width]
    (instruction : WordLangInst (BitVec width)) (bound : Nat)
    (maximum : maxVarInstHOL instruction ≤ bound) :
    everyVarInstHOL (fun x => decide (x ≤ bound)) instruction = true := by
  apply everyVarInstMono _ instruction (fun x => decide (x ≤ bound))
  refine ⟨?_, maxVarInstMax instruction⟩
  intro x bounded
  simp only [decide_eq_true_eq] at bounded ⊢
  exact Nat.le_trans bounded maximum

/-- Flapjack induction infrastructure for both exact Spt key enumerations;
no well-formedness or finite-map representation premise is added. -/
private theorem namesBound (names : WordLangCutsetsHOL) (bound : Nat)
    (maximum : cutsetsMaxHOL names ≤ bound) :
    everyNameHOL (fun x => decide (x ≤ bound)) names = true := by
  simp only [cutsetsMaxHOL, Nat.max_le] at maximum
  simp only [everyNameHOL, Bool.and_eq_true]
  exact ⟨listBound _ bound maximum.1, listBound _ bound maximum.2⟩

/-- Flapjack induction infrastructure strengthening the original result to any
larger bound; the public theorem instantiates the actual maximum. -/
private theorem programBound {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) :
    ∀ bound, maxVarHOL program ≤ bound →
      everyVarHOL (fun x => decide (x ≤ bound)) program = true := by
  induction program using maxVarHOL.induct
  case case27 =>
    rename_i remaining
      excluded1 excluded2 excluded3 excluded4 excluded5 excluded6
      excluded7 excluded8 excluded9 excluded10 excluded11 excluded12
      excluded13 excluded14 excluded15 excluded16 excluded17 excluded18
      excluded19 excluded20 excluded21 excluded22 excluded23 excluded24
    intro bound maximum
    cases remaining <;> try rfl
    all_goals exfalso
    all_goals solve_by_elim
  case case12 operator left right first second ihFirst ihSecond =>
    intro bound maximum
    have firstAtBound := ihFirst bound
    have secondAtBound := ihSecond bound
    cases right <;>
      simp only [maxVarHOL, Flapjack.WordAlloc.max3Eq, Nat.max_le] at maximum
    all_goals simp only [everyVarHOL, everyVarImmHOL, Bool.and_eq_true, decide_eq_true_eq]
    all_goals aesop (config := { enableSimp := false }) (add safe apply [True.intro])
  all_goals intro bound maximum
  all_goals try
    rename_i ihFirst ihSecond
    have firstAtBound := ihFirst bound
    have secondAtBound := ihSecond bound
  all_goals try
    rename_i ih
    have atBound := ih bound
  all_goals try simp only [maxVarHOL, Flapjack.WordAlloc.max3Eq, maxList_append,
    maxList, Nat.max_le] at maximum
  all_goals try simp only [everyVarHOL, Bool.and_eq_true, decide_eq_true_eq]
  all_goals aesop (config := { enableSimp := false }) (add safe apply [True.intro, listBound, expressionBound, instructionBound, namesBound])

/-- Every register observed by the complete native occurrence predicate is
bounded by the actual program maximum. This is the original unconditional
program result, including return-dependent Call handler traversal. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem maxVarMax {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) :
    everyVarHOL (fun x => decide (x ≤ maxVarHOL program)) program = true :=
  programBound program _ (Nat.le_refl _)

end Flapjack.Compiler.Backend.WordAlloc
