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

private theorem mapM_success_eq (xs : List Exp) (env : List Nat) (d fuel : Nat)
    (ih : ∀ e result, compileFuel fuel env d e = some result → result = compileSing env d e)
    (ys : List Exp) (run : xs.mapM (compileFuel fuel env d) = some ys) :
    ys = compileList env d xs := by
  induction xs generalizing ys with
  | nil => simpa [compileList] using run.symm
  | cons x xs rec =>
    simp only [List.mapM_cons] at run
    cases hx : compileFuel fuel env d x with
    | none => simp [hx] at run
    | some value =>
      cases ht : xs.mapM (compileFuel fuel env d) with
      | none => simp [hx, ht] at run
      | some tail =>
        simp [hx, ht] at run
        subst ys
        rw [ih x value hx, rec tail ht]
        simp [compileList]

private theorem nonVarLet_success (fuel : Nat) (env : List Nat) (d : Nat)
    (x : Exp) (xs : List Exp) (body result : Exp)
    (notVar : ∀ v, body ≠ .var v)
    (ih : ∀ env d exp result, compileFuel fuel env d exp = some result → result = compileSing env d exp)
    (run : compileFuel (fuel + 1) env d (.let (x :: xs) body) = some result) :
    result = compileSing env d (.let (x :: xs) body) := by
  cases bindingsRun : (x :: xs).mapM (compileFuel fuel env d) with
  | none =>
    cases body with
    | var v => exact False.elim (notVar v rfl)
    | _ =>
      simp only [compileFuel, bindingsRun] at run
      simp at run
  | some bindings =>
    have bindingsEq := mapM_success_eq (x :: xs) env d fuel (ih env d) bindings bindingsRun
    cases bodyRun : compileFuel fuel (extractList bindings ++ env) d body with
    | none => cases body <;> simp_all [compileFuel]
    | some value =>
      have bodyEq := ih (extractList bindings ++ env) d body value bodyRun
      cases body <;> simp_all [compileFuel, compileSing]

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
fuel already exceeds the structural bound. -/
theorem compileBounded_eq_compileSing_of_bound (fuel : Nat) (env : List Nat) (d : Nat) (exp : Exp)
    (bound : expBudget exp < fuel) :
    compileBounded fuel env d exp = some (compileSing env d exp) := by
  simp [compileBounded, compileFuel_eq_compileSing fuel env d exp bound]

/-- Every successful traversal agrees with the total source-shaped optimizer,
regardless of the amount of fuel supplied. -/
theorem compileFuel_success_eq (fuel : Nat) (env : List Nat) (d : Nat)
    (exp result : Exp) (run : compileFuel fuel env d exp = some result) :
    result = compileSing env d exp := by
  induction fuel generalizing env d exp result with
  | zero => simp [compileFuel] at run
  | succ fuel ih =>
    cases exp with
    | var v => simpa [compileFuel, compileSing] using run.symm
    | force loc v => simpa [compileFuel, compileSing] using run.symm
    | raise body =>
      cases bodyRun : compileFuel fuel env d body with
      | none => simp [compileFuel, bodyRun] at run
      | some value =>
        have eq := ih env d body value bodyRun
        simpa [compileFuel, compileSing, bodyRun, eq] using run.symm
    | tick body =>
      cases bodyRun : compileFuel fuel env d body with
      | none => simp [compileFuel, bodyRun] at run
      | some value =>
        have eq := ih env d body value bodyRun
        simpa [compileFuel, compileSing, bodyRun, eq] using run.symm
    | ifThenElse x y z =>
      cases hx : compileFuel fuel env d x with
      | none => simp [compileFuel, hx] at run
      | some xv =>
        cases hy : compileFuel fuel env d y with
        | none => simp [compileFuel, hx, hy] at run
        | some yv =>
          cases hz : compileFuel fuel env d z with
          | none => simp [compileFuel, hx, hy, hz] at run
          | some zv =>
            have ex := ih env d x xv hx
            have ey := ih env d y yv hy
            have ez := ih env d z zv hz
            simpa [compileFuel, compileSing, hx, hy, hz, ex, ey, ez] using run.symm
    | op op xs =>
      cases h : xs.mapM (compileFuel fuel env d) with
      | none => simp [compileFuel, h] at run
      | some ys =>
        have eq := mapM_success_eq xs env d fuel (ih env d) ys h
        simpa [compileFuel, compileSing, h, eq] using run.symm
    | «return» xs =>
      cases h : xs.mapM (compileFuel fuel env d) with
      | none => simp [compileFuel, h] at run
      | some ys =>
        have eq := mapM_success_eq xs env d fuel (ih env d) ys h
        simpa [compileFuel, compileSing, h, eq] using run.symm
    | call ticks dest xs handler =>
      cases h : xs.mapM (compileFuel fuel env d) with
      | none => simp [compileFuel, h] at run
      | some ys =>
        have eq := mapM_success_eq xs env d fuel (ih env d) ys h
        cases handler with
        | none => simpa [compileFuel, compileSing, h, eq] using run.symm
        | some handler =>
          cases hh : compileFuel fuel (0 :: env) d handler with
          | none => simp [compileFuel, h, hh] at run
          | some value =>
            have eh := ih (0 :: env) d handler value hh
            simpa [compileFuel, compileSing, h, hh, eq, eh] using run.symm
    | letCall rets ticks dest xs body =>
      cases h : xs.mapM (compileFuel fuel env d) with
      | none => simp [compileFuel, h] at run
      | some ys =>
        have eq := mapM_success_eq xs env d fuel (ih env d) ys h
        cases hb : compileFuel fuel (List.replicate rets 0 ++ env) d body with
        | none => simp [compileFuel, h, hb] at run
        | some value =>
          have eb := ih (List.replicate rets 0 ++ env) d body value hb
          simpa [compileFuel, compileSing, h, hb, eq, eb] using run.symm
    | «let» xs body =>
      cases xs with
      | nil =>
        cases hb : compileFuel fuel env d body with
        | none => simp [compileFuel, hb] at run
        | some value =>
          have eq := ih env d body value hb
          simpa [compileFuel, compileSing, hb, eq] using run.symm
      | cons x xs =>
        cases body with
        | var v =>
          by_cases eq : v = xs.length
          · let last : Exp := (x :: xs).getLast (by simp)
            have hlast : (x :: xs).getLast? = some last :=
              List.getLast?_eq_some_getLast (show x :: xs ≠ [] by simp)
            cases earlierRun : (x :: xs).dropLast.mapM (compileFuel fuel env d) with
            | none => simp [compileFuel, eq, hlast, earlierRun] at run
            | some earlier =>
              have earlierEq := mapM_success_eq (x :: xs).dropLast env d fuel (ih env d) earlier earlierRun
              cases tailRun : compileFuel fuel (env.map (xs.length + ·)) (d + xs.length) last with
              | none => simp [compileFuel, eq, hlast, earlierRun, tailRun] at run
              | some tail =>
                have tailEq := ih (env.map (xs.length + ·)) (d + xs.length) last tail tailRun
                simpa [compileFuel, compileSing, eq, hlast, earlierRun, tailRun, earlierEq, tailEq, last] using run.symm
          · cases bindingsRun : (x :: xs).mapM (compileFuel fuel env d) with
            | none => simp [compileFuel, eq, bindingsRun] at run
            | some bindings =>
              have bindingsEq := mapM_success_eq (x :: xs) env d fuel (ih env d) bindings bindingsRun
              cases bodyRun : compileFuel fuel (extractList bindings ++ env) d (.var v) with
              | none => simp [compileFuel, eq, bindingsRun, bodyRun] at run
              | some value =>
                have bodyEq := ih (extractList bindings ++ env) d (.var v) value bodyRun
                simp [compileFuel, eq, bindingsRun, bodyRun] at run
                subst result
                subst bindings
                simpa [compileSing, eq] using bodyEq
        | _ =>
          apply nonVarLet_success fuel env d x xs _ result ?_ ih run
          intro v
          simp

/-- The executed retry agrees with the total source-shaped optimizer for
every initial fuel, including successful traversals below the sufficient
bound. This is Flapjack infrastructure, with no separate HOL counterpart. -/
theorem compileBounded_eq_compileSing (fuel : Nat) (env : List Nat) (d : Nat) (exp : Exp) :
    compileBounded fuel env d exp = some (compileSing env d exp) := by
  cases run : compileFuel fuel env d exp with
  | some result =>
    have eq := compileFuel_success_eq fuel env d exp result run
    simp [compileBounded, run, eq]
  | none =>
    have bound : expBudget exp < max fuel (expBudget exp + 1) := by omega
    simp [compileBounded, run, compileFuel_eq_compileSing _ env d exp bound]

end Flapjack.Compiler.Backend.BviLet
