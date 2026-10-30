import Flapjack.Compiler.Backend.BviLet.SourceSing
import Flapjack.Compiler.Backend.BviLet.Proofs.Total

/-! Agreement between the total source-shaped optimizer and the executable. -/
namespace Flapjack.Compiler.Backend.BviLet
open Bvi

private theorem memberBudget (xs : List Exp) (e : Exp) (member : e ∈ xs) :
    expBudget e < listBudget xs := by
  induction xs with
  | nil => simp at member
  | cons x xs ih =>
    simp only [List.mem_cons] at member
    simp only [listBudget]
    rcases member with rfl | member
    · omega
    · have := ih member; omega

private theorem mapM_eq_compileList (xs : List Exp) (env : List Nat) (d fuel : Nat)
    (h : ∀ e ∈ xs, compileFuel fuel env d e = some (compileSing env d e)) :
    xs.mapM (compileFuel fuel env d) = some (compileList env d xs) := by
  induction xs with
  | nil => simp [compileList]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (by intro e member; exact h e (by simp [member]))
    simp [List.mapM_cons, compileList, hx, ht]

/-- Sufficient traversal fuel agrees with the total source-shaped optimizer.
This is Flapjack infrastructure; HOL correspondence is reviewed separately. -/
theorem compileFuel_eq_compileSing (fuel : Nat) (env : List Nat) (d : Nat) (exp : Exp)
    (bound : expBudget exp < fuel) :
    compileFuel fuel env d exp = some (compileSing env d exp) := by
  induction fuel generalizing env d exp with
  | zero => omega
  | succ fuel ih =>
    cases exp with
    | var v => simp [compileFuel, compileSing]
    | force loc v => simp [compileFuel, compileSing]
    | ifThenElse x y z =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      have bz : expBudget z < fuel := by simp_all [expBudget] <;> omega
      simp [compileFuel, compileSing, ih env d x bx, ih env d y by', ih env d z bz]
    | raise x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      simp [compileFuel, compileSing, ih env d x bx]
    | tick x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      simp [compileFuel, compileSing, ih env d x bx]
    | op op xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have h := mapM_eq_compileList xs env d fuel (by
        intro e he; apply ih; have := memberBudget xs e he; omega)
      simp [compileFuel, compileSing, h]
    | «return» xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have h := mapM_eq_compileList xs env d fuel (by
        intro e he; apply ih; have := memberBudget xs e he; omega)
      simp [compileFuel, compileSing, h]
    | call ticks dest xs handler =>
      cases handler with
      | none =>
        have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
        have h := mapM_eq_compileList xs env d fuel (by
          intro e he; apply ih; have := memberBudget xs e he; omega)
        simp [compileFuel, compileSing, h]
      | some handler =>
        have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
        have bh : expBudget handler < fuel := by simp_all [expBudget] <;> omega
        have h := mapM_eq_compileList xs env d fuel (by
          intro e he; apply ih; have := memberBudget xs e he; omega)
        simp [compileFuel, compileSing, h, ih (0 :: env) d handler bh]
    | letCall rets ticks dest xs body =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      have h := mapM_eq_compileList xs env d fuel (by
        intro e he; apply ih; have := memberBudget xs e he; omega)
      simp [compileFuel, compileSing, h, ih (List.replicate rets 0 ++ env) d body bb]
    | «let» xs body =>
      cases xs with
      | nil =>
        have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
        simp [compileFuel, compileSing, ih env d body bb]
      | cons x xs =>
        have bx : listBudget (x :: xs) < fuel := by simp_all [expBudget] <;> omega
        have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
        have each : ∀ e ∈ x :: xs, expBudget e < fuel := by
          intro e he; have := memberBudget (x :: xs) e he; omega
        have allBindings := mapM_eq_compileList (x :: xs) env d fuel (by
          intro e he; exact ih env d e (each e he))
        cases body with
        | var v =>
          by_cases eq : v = xs.length
          · have hlast := List.getLast?_eq_some_getLast (show x :: xs ≠ [] by simp)
            have lastMem := List.getLast_mem (show x :: xs ≠ [] by simp)
            have earlier := mapM_eq_compileList (x :: xs).dropLast env d fuel (by
              intro e he; exact ih env d e (each e (List.dropLast_subset _ he)))
            have last := ih (env.map (xs.length + ·)) (d + xs.length)
              ((x :: xs).getLast (by simp)) (each _ lastMem)
            simp [compileFuel, compileSing, eq, hlast, earlier, last]
          · have bodyResult := ih (extractList (compileList env d (x :: xs)) ++ env) d (.var v) bb
            simp [compileFuel, compileSing, eq, allBindings, bodyResult]
        | _ =>
          have bodyResult := ih (extractList (compileList env d (x :: xs)) ++ env) d _ bb
          simp [compileFuel, compileSing, allBindings, bodyResult]

/-- The production retry agrees with the total optimizer when its initial
fuel already exceeds the structural bound. The arbitrary-fuel case remains
open pending a proof that every successful low-fuel traversal is stable. -/
theorem compileBounded_eq_compileSing_of_bound (fuel : Nat) (env : List Nat) (d : Nat) (exp : Exp)
    (bound : expBudget exp < fuel) :
    compileBounded fuel env d exp = some (compileSing env d exp) := by
  simp [compileBounded, compileFuel_eq_compileSing fuel env d exp bound]

end Flapjack.Compiler.Backend.BviLet
