import Flapjack.Compiler.Backend.BvlConst.Compile
import Flapjack.Compiler.Backend.BvlConst.Proofs.Total
import Aesop

/-! Correspondence between executable and total constant-propagation
traversals. This is Flapjack infrastructure, not a HOL theorem. -/
namespace Flapjack.Compiler.Backend.BvlConst
open Bvl BvlToBvi

private theorem mapM_eq_compileList (visit : Exp → Option Exp) (env : List (Option Exp))
    (correct : ∀ e result, visit e = some result → result = compileSing env e)
    (xs ys : List Exp) (run : xs.mapM visit = some ys) : ys = compileList env xs := by
  induction xs generalizing ys with
  | nil => simpa [compileList] using run.symm
  | cons x rest ih =>
    simp only [List.mapM_cons] at run
    cases first : visit x with
    | none => simp [first] at run
    | some value =>
      cases remaining : rest.mapM visit with
      | none => simp [first, remaining] at run
      | some values =>
        simp [first, remaining] at run
        subst ys
        simp [compileList, correct x value first, ih values remaining]

/-- Every successful bounded traversal equals the total traversal. -/
theorem compileFuel_eq (fuel : Nat) :
    ∀ env e result, compileFuel fuel env e = some result → result = compileSing env e := by
  induction fuel with
  | zero => simp [compileFuel]
  | succ fuel ih =>
    intro env e result run
    cases e <;> simp only [compileFuel] at run <;> try simp only [compileSing]
    case ifThenElse x y z =>
      cases hx : compileFuel fuel env x with
      | none => simp [hx] at run
      | some x' =>
        have ex := ih env x x' hx
        cases hy : compileFuel fuel env y with
        | none => simp [hx, hy] at run
        | some y' =>
          have ey := ih env y y' hy
          cases hz : compileFuel fuel env z with
          | none => simp [hx, hy, hz] at run
          | some z' =>
            have ez := ih env z z' hz
            simp only [← ex, ← ey, ← ez]
            simp only [hx, hy, hz, bind, Option.bind] at run
            clear ex ey ez hx hy hz
            split at run <;> simp_all
    case «let» xs y =>
      cases hx : xs.mapM (compileFuel fuel env) with
      | none => simp [hx] at run
      | some xs' =>
        have ex := mapM_eq_compileList (compileFuel fuel env) env (ih env) xs xs' hx
        cases hy : compileFuel fuel (extractList xs' ++ env) y with
        | none => simp [hx, hy] at run
        | some y' =>
          have ey := ih (extractList xs' ++ env) y y' hy
          simpa [hx, hy, ← ex, ← ey] using run.symm
    case op op xs =>
      cases hx : xs.mapM (compileFuel fuel env) with
      | none => simp [hx] at run
      | some xs' =>
        have ex := mapM_eq_compileList (compileFuel fuel env) env (ih env) xs xs' hx
        simpa [hx, ← ex] using run.symm
    all_goals try (simp only [bind, Option.bind] at run)
    all_goals repeat' split at run
    all_goals try simp_all
    all_goals aesop (add safe apply mapM_eq_compileList)

/-- The retrying traversal always returns the total traversal's result. -/
theorem compileBounded_eq (fuel : Nat) (env : List (Option Exp)) (e : Exp) :
    compileBounded fuel env e = some (compileSing env e) := by
  cases run : compileFuel fuel env e with
  | some result =>
    have correct := compileFuel_eq fuel env e result run
    simp [compileBounded, run, correct]
  | none =>
    obtain ⟨result, success⟩ := compileFuel_succeeds
      (max fuel (expBudget e + 1)) env e (by omega)
    have correct := compileFuel_eq _ env e result success
    simp [compileBounded, run, success, correct]

end Flapjack.Compiler.Backend.BvlConst
