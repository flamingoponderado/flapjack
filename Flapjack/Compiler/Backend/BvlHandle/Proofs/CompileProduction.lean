import Flapjack.Compiler.Backend.BvlHandle.Compile
import Flapjack.Compiler.Backend.BvlHandle.Proofs.CompileTotal

/-! The fuel-bounded compiler agrees with the source-shaped total traversal. -/
namespace Flapjack.Compiler.Backend.BvlHandle
open Bvl DbVars BvlToBvi

/-- Successful fuel-bounded traversals compute the source result. -/
theorem compileFuel_eq (fuel : Nat) :
    (∀ limit env e result, compileFuel fuel limit env e = some result →
      result = compileSing limit env e) ∧
    (∀ limit env xs result, compileListFuel fuel limit env xs = some result →
      result = compileList limit env xs) := by
  induction fuel with
  | zero =>
    constructor
    · intro limit env e result run
      simp [compileFuel] at run
    · intro limit env xs result run
      cases xs <;> simp_all [compileListFuel, compileList]
  | succ fuel ih =>
    constructor
    · intro limit env e result run
      cases e with
      | var v =>
        by_cases h : v < env <;> simpa [compileFuel, compileSing, zero, h] using run.symm
      | force m v =>
        by_cases h : v < env <;> simpa [compileFuel, compileSing, zero, h] using run.symm
      | ifThenElse x y z =>
        cases hx : compileFuel fuel limit env x with
        | none => simp [compileFuel, hx] at run
        | some xr =>
          have ex := ih.1 limit env x xr hx
          cases hy : compileFuel fuel limit env y with
          | none => simp [compileFuel, hx, hy] at run
          | some yr =>
            have ey := ih.1 limit env y yr hy
            cases hz : compileFuel fuel limit env z with
            | none => simp [compileFuel, hx, hy, hz] at run
            | some zr =>
              have ez := ih.1 limit env z zr hz
              rcases xr with ⟨x', lx, sx, nx⟩
              rcases yr with ⟨y', ly, sy, ny⟩
              rcases zr with ⟨z', lz, sz, nz⟩
              simpa [compileFuel, compileSing, hx, hy, hz, ← ex, ← ey, ← ez] using run.symm
      | «let» xs body =>
        cases xs with
        | nil =>
          simp only [compileFuel] at run
          simpa [compileSing] using ih.1 limit env body result run
        | cons x xs =>
          cases hx : compileListFuel fuel limit env (x :: xs) with
          | none => simp [compileFuel, hx] at run
          | some xr =>
            have ex := ih.2 limit env (x :: xs) xr hx
            cases hy : compileFuel fuel limit (env + (x :: xs).length) body with
            | none =>
              simp only [List.length_cons] at hy
              simp [compileFuel, hx, hy] at run
            | some yr =>
              have ey := ih.1 limit (env + (x :: xs).length) body yr hy
              simp only [List.length_cons] at hy ey
              rcases xr with ⟨xs', lx, sx, nx⟩
              rcases yr with ⟨body', ly, sy, ny⟩
              simpa [compileFuel, compileSing, hx, hy, ← ex, ← ey] using run.symm
      | handle x y =>
        cases hx : compileFuel fuel limit env x with
        | none => simp [compileFuel, hx] at run
        | some xr =>
          have ex := ih.1 limit env x xr hx
          rcases xr with ⟨x', lx, sx, nx⟩
          cases nx with
          | true => simpa [compileFuel, compileSing, hx, ← ex] using run.symm
          | false =>
            cases hy : compileFuel fuel limit (env + 1) y with
            | none => simp [compileFuel, hx, hy] at run
            | some yr =>
              have ey := ih.1 limit (env + 1) y yr hy
              rcases yr with ⟨y', ly, sy, ny⟩
              simpa [compileFuel, compileSing, hx, hy, ← ex, ← ey] using run.symm
      | raise x =>
        cases hx : compileFuel fuel limit env x with
        | none => simp [compileFuel, hx] at run
        | some xr =>
          have ex := ih.1 limit env x xr hx
          rcases xr with ⟨x', lx, sx, nx⟩
          simpa [compileFuel, compileSing, hx, ← ex] using run.symm
      | tick x =>
        cases hx : compileFuel fuel limit env x with
        | none => simp [compileFuel, hx] at run
        | some xr =>
          have ex := ih.1 limit env x xr hx
          rcases xr with ⟨x', lx, sx, nx⟩
          simpa [compileFuel, compileSing, hx, ← ex] using run.symm
      | op op xs =>
        cases hx : compileListFuel fuel limit env xs with
        | none => simp [compileFuel, hx] at run
        | some xr =>
          have ex := ih.2 limit env xs xr hx
          rcases xr with ⟨xs', lx, sx, nx⟩
          cases op <;> try (simpa [compileFuel, compileSing, hx, ← ex] using run.symm)
          case thunkOp thunk =>
            cases thunk <;> simpa [compileFuel, compileSing, hx, ← ex] using run.symm
      | call ticks dest xs =>
        cases hx : compileListFuel fuel limit env xs with
        | none => simp [compileFuel, hx] at run
        | some xr =>
          have ex := ih.2 limit env xs xr hx
          rcases xr with ⟨xs', lx, sx, nx⟩
          simpa [compileFuel, compileSing, hx, ← ex] using run.symm
    · intro limit env xs result run
      cases xs with
      | nil => simpa [compileListFuel, compileList] using run.symm
      | cons x xs =>
        cases hx : compileFuel fuel limit env x with
        | none => simp [compileListFuel, hx] at run
        | some xr =>
          have ex := ih.1 limit env x xr hx
          cases hy : compileListFuel fuel limit env xs with
          | none => simp [compileListFuel, hx, hy] at run
          | some yr =>
            have ey := ih.2 limit env xs yr hy
            rcases xr with ⟨x', lx, sx, nx⟩
            rcases yr with ⟨xs', ly, sy, ny⟩
            simpa [compileListFuel, compileList, hx, hy, ← ex, ← ey] using run.symm

/-- The executable retry returns the source singleton compiler's result. -/
theorem compileBounded_eq (fuel limit env : Nat) (e : Exp) :
    compileBounded fuel limit env e = some (compileSing limit env e) := by
  cases run : compileFuel fuel limit env e with
  | some result =>
    rw [compileBounded, run]
    rw [(compileFuel_eq fuel).1 limit env e result run]
  | none =>
    obtain ⟨result, success⟩ := compileFuel_succeeds
      (max fuel (expBudget e + 1)) limit env e (by omega)
    rw [compileBounded, run, success]
    rw [(compileFuel_eq _).1 limit env e result success]

end Flapjack.Compiler.Backend.BvlHandle
