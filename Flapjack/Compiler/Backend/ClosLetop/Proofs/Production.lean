import Flapjack.Misc.Option.MapM
import Flapjack.Compiler.Backend.ClosLetop.Source
import Flapjack.Compiler.Backend.ClosLetop.Proofs.Total
import Mathlib.Tactic

/-! Agreement of executable let-operation cleanup with the source traversal. -/
namespace Flapjack.Compiler.Backend.ClosLetop
open ClosLang

/-- A list traversal is the pointwise source traversal. This is Flapjack
infrastructure for the production agreement proof. -/
theorem compileList_eq_map (expressions : List Exp) :
    compileList expressions = expressions.map compileSing := by
  induction expressions with
  | nil => rfl
  | cons first rest ih => simp [compileList, ih]

/-- Recursive bodies retain their arities. This is Flapjack infrastructure
for the production agreement proof. -/
theorem compileFuns_eq_map (functions : List (Nat × Exp)) :
    compileFuns functions = functions.map (fun (arity, body) => (arity, compileSing body)) := by
  induction functions with
  | nil => rfl
  | cons function rest ih =>
    obtain ⟨arity, body⟩ := function
    simp [compileFuns, ih]

private theorem varList_range {α : Type} (args : List α) (xs : List Exp) (n : Nat) :
    varList n xs args =
      ((xs.length == args.length) && (xs.zip (List.range' n args.length)).all fun (x, i) =>
        match x with | .var _ m => m == i | _ => false) := by
  induction args generalizing xs n with
  | nil => cases xs <;> simp [varList]
  | cons arg rest ih =>
    cases xs with
    | nil => simp [varList]
    | cons x xs =>
      cases x <;> simp [varList, List.range'_succ, ih, Bool.and_left_comm, Bool.and_comm]

/-- The executed arity-based check agrees with the original list check for
every expression list and binding list. This is Flapjack infrastructure. -/
theorem varListArity_eq_source {α : Type} (xs : List Exp) (args : List α) :
    varListArity xs args.length = varList 0 xs args := by
  rw [varList_range]
  simp [varListArity, List.range_eq_range']
  rfl

/-- Every successful bounded traversal returns the source traversal. This is
Flapjack infrastructure for the production agreement proof. -/
theorem compileFuel_eq_source (fuel : Nat) (expression result : Exp)
    (run : compileFuel fuel expression = some result) : result = compileSing expression := by
  induction fuel generalizing expression result with
  | zero => simp [compileFuel] at run
  | succ fuel ih =>
    cases expression
    case «let» trace xs body =>
      cases xsRun : xs.mapM (compileFuel fuel) with
      | none => simp [compileFuel, xsRun] at run
      | some ys =>
        cases bodyRun : compileFuel fuel body with
        | none => simp [compileFuel, xsRun, bodyRun] at run
        | some nextBody =>
          have ysEq := mapM_eq_map (compileFuel fuel) compileSing ih xs ys xsRun
          have bodyEq := ih body nextBody bodyRun
          simp only [compileFuel, xsRun, bodyRun, bind, Option.bind] at run
          simp only [compileSing, compileList_eq_map]
          rw [← ysEq, ← bodyEq]
          cases nextBody <;> simp [destOp, varListArity_eq_source] at run ⊢ <;>
            (try split at run) <;> simp_all
    all_goals simp only [compileFuel] at run
    all_goals simp only [compileSing]
    all_goals try (simp only [bind, Option.bind] at run)
    all_goals repeat' split at run
    all_goals try simp_all [compileList_eq_map, compileFuns_eq_map]
    all_goals aesop (add safe apply mapM_eq_map)

/-- The production retry returns the source traversal for every fuel value.
This is Flapjack infrastructure for the production agreement proof. -/
theorem compileBounded_eq_source (fuel : Nat) (expression : Exp) :
    compileBounded fuel expression = some (compileSing expression) := by
  obtain ⟨result, run⟩ := compileBounded_succeeds fuel expression
  unfold compileBounded at run ⊢
  cases first : compileFuel fuel expression with
  | some value =>
    have equal := compileFuel_eq_source fuel expression value first
    simp [equal]
  | none =>
    have retry : compileFuel (max fuel (expBudget expression + 1)) expression = some result := by
      simpa [first] using run
    have equal := compileFuel_eq_source _ expression result retry
    simpa [first, equal] using retry

/-- The production list traversal returns the source-shaped list traversal.
This is Flapjack infrastructure for the production agreement proof. -/
theorem compileBounded_list_eq_source (fuel : Nat) (expressions : List Exp) :
    expressions.mapM (compileBounded fuel) = some (compileList expressions) := by
  induction expressions with
  | nil => rfl
  | cons first rest ih => simp [compileList, compileBounded_eq_source, ih]

end Flapjack.Compiler.Backend.ClosLetop
