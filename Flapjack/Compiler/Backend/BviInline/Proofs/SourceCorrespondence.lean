import Flapjack.Compiler.Backend.BviInline.Source
import Flapjack.Compiler.Backend.BviInline.Proofs.Total

/-! Correspondence between source-shaped and executed BVI traversals. -/
namespace Flapjack.Compiler.Backend.BviInline
open Bvi

/-- Flapjack infrastructure: sufficient fuel makes the executed tick remover
equal the total source-shaped traversal on every expression. -/
theorem removeTicksFuel_eq_source (fuel : Nat) (expression : Exp)
    (bound : expBudget expression < fuel) : removeTicksFuel fuel expression = some (removeTicksSource expression) := by
  induction fuel generalizing expression with
  | zero => omega
  | succ fuel ih =>
    have mapRun : ∀ xs, listBudget xs < fuel →
        xs.mapM (removeTicksFuel fuel) = some (removeTicksListSource xs) := by
      intro xs bound
      induction xs with
      | nil => simp [removeTicksListSource]
      | cons e es tail =>
        have headBound : expBudget e < fuel := by simp [listBudget] at bound; omega
        have tailBound : listBudget es < fuel := by simp [listBudget] at bound; omega
        simp [removeTicksListSource, List.mapM_cons, ih e headBound, tail tailBound]
    cases expression with
    | var n => simp [removeTicksFuel, removeTicksSource]
    | force loc n => simp [removeTicksFuel, removeTicksSource]
    | ifThenElse x y z =>
      have bx : expBudget x < fuel := by simp [expBudget] at bound; omega
      have by' : expBudget y < fuel := by simp [expBudget] at bound; omega
      have bz : expBudget z < fuel := by simp [expBudget] at bound; omega
      simp [removeTicksFuel, removeTicksSource, ih x bx, ih y by', ih z bz]
    | «let» xs body =>
      have bx : listBudget xs < fuel := by simp [expBudget] at bound; omega
      have bb : expBudget body < fuel := by simp [expBudget] at bound; omega
      simp [removeTicksFuel, removeTicksSource, mapRun xs bx, ih body bb]
    | raise body =>
      have bb : expBudget body < fuel := by simp [expBudget] at bound; omega
      simp [removeTicksFuel, removeTicksSource, ih body bb]
    | tick body =>
      have bb : expBudget body < fuel := by simp [expBudget] at bound; omega
      simpa [removeTicksFuel, removeTicksSource] using ih body bb
    | call ticks target xs handler =>
      cases handler with
      | none =>
        have bx : listBudget xs < fuel := by simp [expBudget] at bound; omega
        simp [removeTicksFuel, removeTicksSource, mapRun xs bx]
      | some body =>
        have bx : listBudget xs < fuel := by simp [expBudget] at bound; omega
        have bb : expBudget body < fuel := by simp [expBudget] at bound; omega
        simp [removeTicksFuel, removeTicksSource, mapRun xs bx, ih body bb]
    | op op xs =>
      have bx : listBudget xs < fuel := by simp [expBudget] at bound; omega
      simp [removeTicksFuel, removeTicksSource, mapRun xs bx]
    | letCall rets ticks target xs body =>
      have bx : listBudget xs < fuel := by simp [expBudget] at bound; omega
      have bb : expBudget body < fuel := by simp [expBudget] at bound; omega
      simp [removeTicksFuel, removeTicksSource, mapRun xs bx, ih body bb]
    | «return» xs =>
      have bx : listBudget xs < fuel := by simp [expBudget] at bound; omega
      simp [removeTicksFuel, removeTicksSource, mapRun xs bx]

/-- Flapjack infrastructure: every successful bounded tick-removal run is
the source-shaped result, including runs below the sufficient budget. -/
theorem removeTicksFuel_sound (fuel : Nat) (expression result : Exp)
    (run : removeTicksFuel fuel expression = some result) : result = removeTicksSource expression := by
  induction fuel generalizing expression result with
  | zero => simp [removeTicksFuel] at run
  | succ fuel ih =>
    have child : ∀ e, removeTicksFuel fuel e = some (removeTicksSource e) ∨ removeTicksFuel fuel e = none := by
      intro e
      cases eq : removeTicksFuel fuel e with
      | none => exact Or.inr rfl
      | some value =>
        have same := ih e value eq
        exact Or.inl (congrArg some same)
    have list : ∀ xs, xs.mapM (removeTicksFuel fuel) = some (removeTicksListSource xs) ∨
        xs.mapM (removeTicksFuel fuel) = none := by
      intro xs
      induction xs with
      | nil => left; simp [removeTicksListSource]
      | cons e es tail =>
        rcases child e with head | head <;> rcases tail with rest | rest
        · left; simp [List.mapM_cons, removeTicksListSource, head, rest]
        · right; simp [List.mapM_cons, head, rest]
        · right; simp [List.mapM_cons, head]
        · right; simp [List.mapM_cons, head]
    cases expression with
    | var n => simpa [removeTicksFuel, removeTicksSource] using run.symm
    | force loc n => simpa [removeTicksFuel, removeTicksSource] using run.symm
    | ifThenElse x y z =>
      rcases child x with hx | hx <;> rcases child y with hy | hy <;> rcases child z with hz | hz <;>
        simp_all [removeTicksFuel, removeTicksSource]
    | «let» xs body =>
      rcases list xs with hx | hx <;> rcases child body with hb | hb <;>
        simp_all [removeTicksFuel, removeTicksSource]
    | raise body =>
      rcases child body with hb | hb <;> simp_all [removeTicksFuel, removeTicksSource]
    | tick body =>
      rcases child body with hb | hb <;> simp_all [removeTicksFuel, removeTicksSource]
    | call ticks target xs handler =>
      cases handler with
      | none => rcases list xs with hx | hx <;> simp_all [removeTicksFuel, removeTicksSource]
      | some body =>
        rcases list xs with hx | hx <;> rcases child body with hb | hb <;>
          simp_all [removeTicksFuel, removeTicksSource]
    | op op xs => rcases list xs with hx | hx <;> simp_all [removeTicksFuel, removeTicksSource]
    | letCall rets ticks target xs body =>
      rcases list xs with hx | hx <;> rcases child body with hb | hb <;>
        simp_all [removeTicksFuel, removeTicksSource]
    | «return» xs => rcases list xs with hx | hx <;> simp_all [removeTicksFuel, removeTicksSource]

/-- Flapjack infrastructure: the production retrying tick remover always
returns the total source-shaped result for any initial fuel. -/
theorem removeTicksBounded_eq_source (fuel : Nat) (expression : Exp) :
    removeTicksBounded fuel expression = some (removeTicksSource expression) := by
  cases run : removeTicksFuel fuel expression with
  | none =>
    have bound : expBudget expression < max fuel (expBudget expression + 1) := by omega
    simp [removeTicksBounded, run, removeTicksFuel_eq_source _ expression bound]
  | some result =>
    have same := removeTicksFuel_sound fuel expression result run
    simp [removeTicksBounded, run, same]

/-- Flapjack infrastructure: production tick removal maps the total
source-shaped traversal over each program entry without changing its label or
arity. -/
theorem removeTicksProgram_eq_source (fuel : Nat) (program : List (Nat × Nat × Exp)) :
    program.mapM (fun (name, arity, body) => do
      pure (name, arity, ← removeTicksBounded fuel body)) =
      some (program.map (fun (name, arity, body) => (name, arity, removeTicksSource body))) := by
  have each : (fun (entry : Nat × Nat × Exp) => do
      pure (entry.1, entry.2.1, ← removeTicksBounded fuel entry.2.2)) =
      (fun entry => some (entry.1, entry.2.1, removeTicksSource entry.2.2)) := by
    funext entry
    simp [removeTicksBounded_eq_source]
  change program.mapM (fun entry => do
    pure (entry.1, entry.2.1, ← removeTicksBounded fuel entry.2.2)) = _
  rw [each]
  exact List.mapM_pure (m := Option) (f := fun (entry : Nat × Nat × Exp) =>
    (entry.1, entry.2.1, removeTicksSource entry.2.2)) (l := program)

/-- Flapjack infrastructure: after inlining, the production program entry
point returns exactly the source-shaped tick cleanup of the intermediate code. -/
theorem compileProgFuel_tick_cleanup (fuel : Nat) (program intermediate : List (Nat × Nat × Exp))
    (cache : Spt (Nat × Exp)) (inlined : inlineAllFuel fuel .ln program = some (cache, intermediate)) :
    compileProgFuel fuel program = some (cache,
      intermediate.map (fun (name, arity, body) => (name, arity, removeTicksSource body))) := by
  unfold compileProgFuel
  rw [inlined]
  change (intermediate.mapM (fun (entry : Nat × Nat × Exp) => do
    pure (entry.1, entry.2.1, ← removeTicksBounded fuel entry.2.2))).bind
      (fun output => some (cache, output)) = _
  rw [removeTicksProgram_eq_source]
  rfl

end Flapjack.Compiler.Backend.BviInline
