module

public import Flapjack.Compiler.Backend.BviToData.CompileSourceAgrees
public import Flapjack.Compiler.Backend.BviToData.Proofs.Total

@[expose] public section

/-! Agreement of the total traversal with the executed bounded traversal. -/
namespace Flapjack.Compiler.Backend.BviToData

private theorem variablesFrom_iff (xs : List Bvi.Exp) (n : Nat) :
    isVariablesFrom xs n = true ↔ xs = (List.range' n xs.length).map Bvi.Exp.var := by
  induction xs generalizing n with
  | nil => simp [isVariablesFrom]
  | cons head tail ih =>
    cases head <;> simp [isVariablesFrom, List.range', ih]

private theorem tailReturn_iff (rets : Nat) (body : Bvi.Exp) :
    isTailReturn rets body = true ↔ body = .return ((List.range rets).map Bvi.Exp.var) := by
  cases body <;> simp [isTailReturn, variablesFrom_iff, List.range_eq_range']
  case «return» xs =>
    constructor
    · rintro ⟨length, eq⟩
      simpa [length] using eq
    · intro eq
      subst xs
      simp


mutual
/-- Sufficient fuel makes the executable single-expression traversal agree
with the total source traversal. -/
theorem compileFuel_agrees (fuel n : Nat) (env : List Nat) (tail : Bool)
    (live : List Nat) (exp : Bvi.Exp) (bound : Bvi.expBudget exp < fuel) :
    compileFuel fuel n env tail live exp = some (compileSing n env tail live exp) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases exp with
    | var v => cases tail <;> simp [compileFuel, compileSing]
    | force loc v => simp [compileFuel, compileSing]
    | ifThenElse x y z =>
      have bx : Bvi.expBudget x < fuel := by simp_all [Bvi.expBudget]; omega
      have byBound : Bvi.expBudget y < fuel := by simp_all [Bvi.expBudget]; omega
      have bz : Bvi.expBudget z < fuel := by simp_all [Bvi.expBudget]; omega
      obtain ⟨⟨cx, vx, n1⟩, hx⟩ := compileFuel_succeeds fuel n env false live x bx
      obtain ⟨⟨cy, vy, n2⟩, hy⟩ := compileFuel_succeeds fuel n1 env tail live y byBound
      obtain ⟨⟨cz, vz, n3⟩, hz⟩ := compileFuel_succeeds fuel n2 env tail live z bz
      have ex := (compileFuel_agrees fuel n env false live x bx).symm.trans hx
      have ey := (compileFuel_agrees fuel n1 env tail live y byBound).symm.trans hy
      have ez := (compileFuel_agrees fuel n2 env tail live z bz).symm.trans hz
      simp only [Option.some.injEq] at ex ey ez
      cases tail <;> simp [compileFuel, compileSing, hx, hy, hz, ex, ey, ez]
    | «let» xs body =>
      have bx : Bvi.listBudget xs < fuel := by simp_all [Bvi.expBudget]; omega
      have bb : Bvi.expBudget body < fuel := by simp_all [Bvi.expBudget]; omega
      obtain ⟨⟨c, vs, n1⟩, hc⟩ := compileListFuel_succeeds fuel n env live xs bx
      obtain ⟨⟨body', v, n2⟩, hb⟩ := compileFuel_succeeds fuel n1 (vs ++ env) tail live body bb
      have ec := (compileListFuel_agrees fuel n env live xs bx).symm.trans hc
      have eb := (compileFuel_agrees fuel n1 (vs ++ env) tail live body bb).symm.trans hb
      simp only [Option.some.injEq] at ec eb
      simp [compileFuel, compileSing, hc, hb, ec, eb]
    | raise x =>
      have bx : Bvi.expBudget x < fuel := by simp_all [Bvi.expBudget]; omega
      obtain ⟨⟨c, v, n1⟩, hc⟩ := compileFuel_succeeds fuel n env false live x bx
      have ec := (compileFuel_agrees fuel n env false live x bx).symm.trans hc
      simp only [Option.some.injEq] at ec
      simp [compileFuel, compileSing, hc, ec]
    | tick x =>
      have bx : Bvi.expBudget x < fuel := by simp_all [Bvi.expBudget]; omega
      obtain ⟨⟨c, v, n1⟩, hc⟩ := compileFuel_succeeds fuel n env tail live x bx
      have ec := (compileFuel_agrees fuel n env tail live x bx).symm.trans hc
      simp only [Option.some.injEq] at ec
      simp [compileFuel, compileSing, hc, ec]
    | «return» xs =>
      have bx : Bvi.listBudget xs < fuel := by simp_all [Bvi.expBudget]; omega
      obtain ⟨⟨c, vs, n1⟩, hc⟩ := compileListFuel_succeeds fuel n env live xs bx
      have ec := (compileListFuel_agrees fuel n env live xs bx).symm.trans hc
      simp only [Option.some.injEq] at ec
      simp [compileFuel, compileSing, hc, ec]
    | op op xs =>
      have bx : Bvi.listBudget xs < fuel := by simp_all [Bvi.expBudget]; omega
      obtain ⟨⟨c, vs, n1⟩, hc⟩ := compileListFuel_succeeds fuel n env live xs bx
      have ec := (compileListFuel_agrees fuel n env live xs bx).symm.trans hc
      simp only [Option.some.injEq] at ec
      simp [compileFuel, compileSing, hc, ec]
    | call ticks dest xs handler =>
      have bx : Bvi.listBudget xs < fuel := by cases handler <;> simp_all [Bvi.expBudget] <;> omega
      obtain ⟨⟨c, vs, n1⟩, hc⟩ := compileListFuel_succeeds fuel n env live xs bx
      have ec := (compileListFuel_agrees fuel n env live xs bx).symm.trans hc
      simp only [Option.some.injEq] at ec
      cases handler with
      | none => simp [compileFuel, compileSing, hc, ec]
      | some h =>
        have bh : Bvi.expBudget h < fuel := by simp_all [Bvi.expBudget]; omega
        obtain ⟨⟨h', v, n2⟩, hh⟩ := compileFuel_succeeds fuel (n1 + 1) (n1 :: env) false live h bh
        have eh := (compileFuel_agrees fuel (n1 + 1) (n1 :: env) false live h bh).symm.trans hh
        simp only [Option.some.injEq] at eh
        simp [compileFuel, compileSing, hc, hh, ec, eh]
    | letCall rets ticks dest xs body =>
      have bx : Bvi.listBudget xs < fuel := by simp_all [Bvi.expBudget]; omega
      have bb : Bvi.expBudget body < fuel := by simp_all [Bvi.expBudget]; omega
      obtain ⟨⟨c, vs, n1⟩, hc⟩ := compileListFuel_succeeds fuel n env live xs bx
      have ec := (compileListFuel_agrees fuel n env live xs bx).symm.trans hc
      simp only [Option.some.injEq] at ec
      by_cases shortcut : body = .return ((List.range rets).map Bvi.Exp.var)
      · subst body
        have hs : isTailReturn rets (.return ((List.range rets).map Bvi.Exp.var)) = true :=
          (tailReturn_iff rets _).mpr rfl
        simp [compileFuel, compileSing, hc, ec, hs]
      · have hs : isTailReturn rets body = false := by
          cases h : isTailReturn rets body with
          | false => rfl
          | true => exact False.elim (shortcut ((tailReturn_iff rets body).mp h))
        obtain ⟨⟨body', v, n2⟩, hb⟩ := compileFuel_succeeds fuel (n1 + rets)
          ((List.range rets).map (n1 + ·) ++ env) tail live body bb
        have eb := (compileFuel_agrees fuel (n1 + rets) ((List.range rets).map (n1 + ·) ++ env)
          tail live body bb).symm.trans hb
        simp only [Option.some.injEq] at eb
        simp [compileFuel, compileSing, hc, hb, ec, eb, hs, shortcut]
termination_by fuel

/-- Sufficient fuel preserves the source list traversal and live-name order. -/
theorem compileListFuel_agrees (fuel n : Nat) (env live : List Nat)
    (xs : List Bvi.Exp) (bound : Bvi.listBudget xs < fuel) :
    compileListFuel fuel n env live xs = some (compileList n env live xs) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases xs with
    | nil => simp [compileListFuel, compileList]
    | cons x xs =>
      have bx : Bvi.expBudget x < fuel := by simp_all [Bvi.listBudget]; omega
      have bxs : Bvi.listBudget xs < fuel := by simp_all [Bvi.listBudget]; omega
      obtain ⟨⟨c, v, n1⟩, hc⟩ := compileFuel_succeeds fuel n env false live x bx
      have ec := (compileFuel_agrees fuel n env false live x bx).symm.trans hc
      simp only [Option.some.injEq] at ec
      cases xs with
      | nil => simp [compileListFuel, compileList, hc, ec]
      | cons y ys =>
        obtain ⟨⟨rest, vs, n2⟩, hr⟩ := compileListFuel_succeeds fuel n1 env (v :: live) (y :: ys) bxs
        have er := (compileListFuel_agrees fuel n1 env (v :: live) (y :: ys) bxs).symm.trans hr
        simp only [Option.some.injEq] at er
        simp [compileListFuel, compileList, hc, hr, ec, er]
termination_by fuel
end


mutual
/-- A successful bounded single-expression compilation has the same result as
its total traversal, regardless of how much fuel was supplied. -/
theorem compileFuel_success_eq (fuel n : Nat) (env : List Nat) (tail : Bool)
    (live : List Nat) (exp : Bvi.Exp) (out : DataLang.Prog × Nat × Nat)
    (run : compileFuel fuel n env tail live exp = some out) :
    out = compileSing n env tail live exp := by
  cases fuel with
  | zero => simp [compileFuel] at run
  | succ fuel =>
    cases exp with
    | var v => cases tail <;> simpa [compileFuel, compileSing] using run.symm
    | force loc v => simpa [compileFuel, compileSing] using run.symm
    | ifThenElse x y z =>
      cases hx : compileFuel fuel n env false live x with
      | none => simp [compileFuel, hx] at run
      | some cx =>
        obtain ⟨cx, vx, n1⟩ := cx
        have ex := compileFuel_success_eq fuel n env false live x (cx, vx, n1) hx
        cases hy : compileFuel fuel n1 env tail live y with
        | none => simp [compileFuel, hx, hy] at run
        | some cy =>
          obtain ⟨cy, vy, n2⟩ := cy
          have ey := compileFuel_success_eq fuel n1 env tail live y (cy, vy, n2) hy
          cases hz : compileFuel fuel n2 env tail live z with
          | none => simp [compileFuel, hx, hy, hz] at run
          | some cz =>
            obtain ⟨cz, vz, n3⟩ := cz
            have ez := compileFuel_success_eq fuel n2 env tail live z (cz, vz, n3) hz
            cases tail <;> simp [compileFuel, compileSing, hx, hy, hz, ← ex, ← ey, ← ez] at run ⊢ <;> exact run.symm
    | «let» xs body =>
      cases hc : compileListFuel fuel n env live xs with
      | none => simp [compileFuel, hc] at run
      | some code =>
        obtain ⟨c, vs, n1⟩ := code
        have ec := compileListFuel_success_eq fuel n env live xs (c, vs, n1) hc
        cases hb : compileFuel fuel n1 (vs ++ env) tail live body with
        | none => simp [compileFuel, hc, hb] at run
        | some compiled =>
          obtain ⟨b, v, n2⟩ := compiled
          have eb := compileFuel_success_eq fuel n1 (vs ++ env) tail live body (b, v, n2) hb
          simpa [compileFuel, compileSing, hc, hb, ← ec, ← eb] using run.symm
    | raise x =>
      cases hx : compileFuel fuel n env false live x with
      | none => simp [compileFuel, hx] at run
      | some compiled =>
        obtain ⟨c, v, n1⟩ := compiled
        have ex := compileFuel_success_eq fuel n env false live x (c, v, n1) hx
        simpa [compileFuel, compileSing, hx, ← ex] using run.symm
    | tick x =>
      cases hx : compileFuel fuel n env tail live x with
      | none => simp [compileFuel, hx] at run
      | some compiled =>
        obtain ⟨c, v, n1⟩ := compiled
        have ex := compileFuel_success_eq fuel n env tail live x (c, v, n1) hx
        simpa [compileFuel, compileSing, hx, ← ex] using run.symm
    | «return» xs =>
      cases hc : compileListFuel fuel n env live xs with
      | none => simp [compileFuel, hc] at run
      | some code =>
        obtain ⟨c, vs, n1⟩ := code
        have ec := compileListFuel_success_eq fuel n env live xs (c, vs, n1) hc
        simpa [compileFuel, compileSing, hc, ← ec] using run.symm
    | op op xs =>
      cases hc : compileListFuel fuel n env live xs with
      | none => simp [compileFuel, hc] at run
      | some code =>
        obtain ⟨c, vs, n1⟩ := code
        have ec := compileListFuel_success_eq fuel n env live xs (c, vs, n1) hc
        simpa [compileFuel, compileSing, hc, ← ec] using run.symm
    | call ticks dest xs handler =>
      cases hc : compileListFuel fuel n env live xs with
      | none => cases handler <;> simp [compileFuel, hc] at run
      | some code =>
        obtain ⟨c, vs, n1⟩ := code
        have ec := compileListFuel_success_eq fuel n env live xs (c, vs, n1) hc
        cases handler with
        | none => simpa [compileFuel, compileSing, hc, ← ec] using run.symm
        | some h =>
          cases hh : compileFuel fuel (n1 + 1) (n1 :: env) false live h with
          | none => simp [compileFuel, hc, hh] at run
          | some compiled =>
            obtain ⟨hcode, v, n2⟩ := compiled
            have eh := compileFuel_success_eq fuel (n1 + 1) (n1 :: env) false live h (hcode, v, n2) hh
            simpa [compileFuel, compileSing, hc, hh, ← ec, ← eh] using run.symm
    | letCall rets ticks dest xs body =>
      cases hc : compileListFuel fuel n env live xs with
      | none => simp [compileFuel, hc] at run
      | some code =>
        obtain ⟨c, vs, n1⟩ := code
        have ec := compileListFuel_success_eq fuel n env live xs (c, vs, n1) hc
        by_cases shortcut : body = .return ((List.range rets).map Bvi.Exp.var)
        · subst body
          have hs : isTailReturn rets (.return ((List.range rets).map Bvi.Exp.var)) = true :=
            (tailReturn_iff rets _).mpr rfl
          simpa [compileFuel, compileSing, hc, ← ec, hs] using run.symm
        · have hs : isTailReturn rets body = false := by
            cases h : isTailReturn rets body with
            | false => rfl
            | true => exact False.elim (shortcut ((tailReturn_iff rets body).mp h))
          cases hb : compileFuel fuel (n1 + rets) ((List.range rets).map (n1 + ·) ++ env) tail live body with
          | none => simp [compileFuel, hc, hs, hb] at run
          | some compiled =>
            obtain ⟨b, v, n2⟩ := compiled
            have eb := compileFuel_success_eq fuel (n1 + rets) ((List.range rets).map (n1 + ·) ++ env)
              tail live body (b, v, n2) hb
            simpa [compileFuel, compileSing, hc, hb, ← ec, ← eb, hs, shortcut] using run.symm
termination_by fuel

/-- A successful bounded operand-list compilation has the same result as the
total traversal, including the order of live locals. -/
theorem compileListFuel_success_eq (fuel n : Nat) (env live : List Nat)
    (xs : List Bvi.Exp) (out : DataLang.Prog × List Nat × Nat)
    (run : compileListFuel fuel n env live xs = some out) : out = compileList n env live xs := by
  cases fuel with
  | zero => simp [compileListFuel] at run
  | succ fuel =>
    cases xs with
    | nil => simpa [compileListFuel, compileList] using run.symm
    | cons x xs =>
      cases hc : compileFuel fuel n env false live x with
      | none => simp [compileListFuel, hc] at run
      | some code =>
        obtain ⟨c, v, n1⟩ := code
        have ec := compileFuel_success_eq fuel n env false live x (c, v, n1) hc
        cases xs with
        | nil => simpa [compileListFuel, compileList, hc, ← ec] using run.symm
        | cons y ys =>
          cases hr : compileListFuel fuel n1 env (v :: live) (y :: ys) with
          | none => simp [compileListFuel, hc, hr] at run
          | some compiled =>
            obtain ⟨rest, vs, n2⟩ := compiled
            have er := compileListFuel_success_eq fuel n1 env (v :: live) (y :: ys) (rest, vs, n2) hr
            simpa [compileListFuel, compileList, hc, hr, ← ec, ← er] using run.symm
termination_by fuel
end

/-- Above the structural budget, the executable wrapper returns the total
source-shaped expression compiler's result. -/
theorem compileExpBounded_agrees (fuel argc : Nat) (exp : Bvi.Exp)
    (bound : Bvi.expBudget exp < fuel) :
    compileExpBounded fuel argc exp = some (compileExp argc exp) := by
  have agreement := compileFuel_agrees fuel argc (List.range argc) true [] exp bound
  have sourceForm := compileSource_agrees argc (List.range argc) true [] [exp]
  simp [compileExpBounded, compileExpFuel, compileExp, agreement, sourceForm]

/-- The retry wrapper agrees with the total compiler at every initial fuel:
successful first attempts are stable, and failed attempts use enough fuel. -/
theorem compileExpBounded_agrees_all (fuel argc : Nat) (exp : Bvi.Exp) :
    compileExpBounded fuel argc exp = some (compileExp argc exp) := by
  have sourceForm := compileSource_agrees argc (List.range argc) true [] [exp]
  cases first : compileFuel fuel argc (List.range argc) true [] exp with
  | some output =>
    obtain ⟨prog, name, next⟩ := output
    have agreement := compileFuel_success_eq fuel argc (List.range argc) true [] exp (prog, name, next) first
    simp [compileExpBounded, compileExpFuel, compileExp, first, ← agreement, sourceForm]
  | none =>
    have bound : Bvi.expBudget exp < max fuel (Bvi.expBudget exp + 1) := by omega
    have agreement := compileFuel_agrees (max fuel (Bvi.expBudget exp + 1)) argc (List.range argc) true [] exp bound
    simp [compileExpBounded, compileExpFuel, compileExp, first, agreement, sourceForm]

/-- Mapping the executed compiler over a BVI program always produces the
same function list as the total source-shaped program compiler. -/
theorem compileProgBounded_agrees (fuel : Nat) (program : List (Nat × Nat × Bvi.Exp)) :
    (program.mapM fun (name, argc, body) => do
      pure (name, argc, ← compileExpBounded fuel argc body)) = some (compileProg program) := by
  induction program with
  | nil => rfl
  | cons part rest ih =>
    obtain ⟨name, argc, body⟩ := part
    simp only [List.mapM_cons]
    rw [ih]
    simp [compileExpBounded_agrees_all, compileProg, compilePart]

end Flapjack.Compiler.Backend.BviToData
