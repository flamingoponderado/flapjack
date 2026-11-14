module

public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.AuxCompiler
public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.FuelStable

@[expose] public section

/-! Relating source auxiliary trees to the executable's flattened lists. -/
namespace Flapjack.Compiler.Backend.BvlToBvi

private theorem destLetBudget (exp : Bvl.Exp) :
    listBudget (destLet exp).1 ≤ expBudget exp ∧ expBudget (destLet exp).2 ≤ expBudget exp := by
  cases exp <;> simp [destLet, expBudget, listBudget] <;> omega

mutual
/-- With sufficient fuel, the executed expression traversal agrees with the
source-shaped conversion after flattening its auxiliary tree. This is
Flapjack infrastructure; it is not a compiler correctness theorem. -/
theorem compileFuel_eq_source (fuel optFuel n : Nat) (exp : Bvl.Exp)
    (bound : expBudget exp < fuel) :
    compileFuel fuel optFuel n exp =
      some ((compileSingSource n exp).1,
        appListAppend (compileSingSource n exp).2.1, (compileSingSource n exp).2.2) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases exp with
    | var v => simp [compileFuel, compileSingSource, appListAppend, appendAux]
    | force loc v => simp [compileFuel, compileSingSource, appListAppend, appendAux]
    | raise x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      rcases hx : compileSingSource n x with ⟨x', a, n1⟩
      have h := compileFuel_eq_source fuel optFuel n x bx
      simp only [hx] at h
      simp [compileFuel, compileSingSource, hx, h]
    | tick x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      rcases hx : compileSingSource n x with ⟨x', a, n1⟩
      have h := compileFuel_eq_source fuel optFuel n x bx
      simp only [hx] at h
      simp [compileFuel, compileSingSource, hx, h]
    | ifThenElse x y z =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      have bz : expBudget z < fuel := by simp_all [expBudget] <;> omega
      rcases hx : compileSingSource n x with ⟨x', a, n1⟩
      rcases hy : compileSingSource n1 y with ⟨y', b, n2⟩
      rcases hz : compileSingSource n2 z with ⟨z', c, n3⟩
      have fx := compileFuel_eq_source fuel optFuel n x bx
      have fy := compileFuel_eq_source fuel optFuel n1 y by'
      have fz := compileFuel_eq_source fuel optFuel n2 z bz
      simp only [hx] at fx
      simp only [hy] at fy
      simp only [hz] at fz
      simp [compileFuel, compileSingSource, hx, hy, hz, fx, fy, fz,
        appListAppend_smartAppend, List.append_assoc]
    | op op xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      rcases hx : compileListSource n xs with ⟨xs', a, n1⟩
      have h := compileListFuel_eq_source fuel optFuel n xs bx
      simp only [hx] at h
      simp [compileFuel, compileSingSource, hx, h]
    | call ticks dest xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      rcases hx : compileListSource n xs with ⟨xs', a, n1⟩
      have h := compileListFuel_eq_source fuel optFuel n xs bx
      simp only [hx] at h
      simp [compileFuel, compileSingSource, hx, h]
    | «let» xs body =>
      cases xs with
      | nil =>
        let args := (destLet body).1
        let inner := (destLet body).2
        have dest : destLet body = (args, inner) := by simp [args, inner]
        have bd := destLetBudget body
        rw [dest] at bd
        have ba : listBudget args < fuel := by simp_all [expBudget, listBudget] <;> omega
        have bi : expBudget inner < fuel := by simp_all [expBudget, listBudget] <;> omega
        rcases ha : compileListSource n args with ⟨args', a, n1⟩
        rcases hb : compileSingSource n1 inner with ⟨inner', b, n2⟩
        have fa := compileListFuel_eq_source fuel optFuel n args ba
        have fb := compileFuel_eq_source fuel optFuel n1 inner bi
        have len := compileListSource_length n args
        simp only [ha] at fa len
        simp only [hb] at fb
        simp [compileFuel, compileSingSource, dest, ha, hb, fa, fb,
          compileAuxFuel_eq_flattened, len, appListAppend_smartAppend, List.append_assoc]
      | cons x xs =>
        have ba : listBudget (x :: xs) < fuel := by simp_all [expBudget] <;> omega
        have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
        rcases ha : compileListSource n (x :: xs) with ⟨args, a, n1⟩
        rcases hb : compileSingSource n1 body with ⟨body', b, n2⟩
        have fa := compileListFuel_eq_source fuel optFuel n (x :: xs) ba
        have fb := compileFuel_eq_source fuel optFuel n1 body bb
        simp only [ha] at fa
        simp only [hb] at fb
        simp [compileFuel, compileSingSource, ha, hb, fa, fb, appListAppend_smartAppend]
    | handle x y =>
      let args := (destLet x).1
      let inner := (destLet x).2
      have dest : destLet x = (args, inner) := by simp [args, inner]
      have bd := destLetBudget x
      rw [dest] at bd
      have ba : listBudget args < fuel := by simp_all [expBudget] <;> omega
      have bi : expBudget inner < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      rcases ha : compileListSource n args with ⟨args', a, n1⟩
      rcases hb : compileSingSource n1 inner with ⟨inner', b, n2⟩
      rcases hc : compileSingSource n2 y with ⟨handler, c, n3⟩
      have fa := compileListFuel_eq_source fuel optFuel n args ba
      have fb := compileFuel_eq_source fuel optFuel n1 inner bi
      have fc := compileFuel_eq_source fuel optFuel n2 y by'
      have len := compileListSource_length n args
      simp only [ha] at fa len
      simp only [hb] at fb
      simp only [hc] at fc
      simp [compileFuel, compileSingSource, dest, ha, hb, hc, fa, fb, fc,
        compileAuxFuel_eq_flattened, len, appListAppend_smartAppend, List.append_assoc]
termination_by fuel

/-- The corresponding list traversal preserves source order and flattens
the source auxiliary tree. -/
theorem compileListFuel_eq_source (fuel optFuel n : Nat) (xs : List Bvl.Exp)
    (bound : listBudget xs < fuel) :
    compileListFuel fuel optFuel n xs =
      some ((compileListSource n xs).1,
        appListAppend (compileListSource n xs).2.1, (compileListSource n xs).2.2) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases xs with
    | nil => simp [compileListFuel, compileListSource, appListAppend, appendAux]
    | cons x xs =>
      have bx : expBudget x < fuel := by simp_all [listBudget] <;> omega
      have bxs : listBudget xs < fuel := by simp_all [listBudget] <;> omega
      rcases hx : compileSingSource n x with ⟨x', a, n1⟩
      rcases hxs : compileListSource n1 xs with ⟨xs', b, n2⟩
      have fx := compileFuel_eq_source fuel optFuel n x bx
      have fxs := compileListFuel_eq_source fuel optFuel n1 xs bxs
      simp only [hx] at fx
      simp only [hxs] at fxs
      simp [compileListFuel, compileListSource, hx, hxs, fx, fxs, appListAppend_smartAppend]
termination_by fuel
end

/-- Every successful executable traversal matches the flattened source result,
even when it succeeds below the structural bound. -/
theorem compileFuel_success_eq_source (fuel optFuel n : Nat) (exp : Bvl.Exp)
    (result : Bvi.Exp × List (Nat × Nat × Bvi.Exp) × Nat)
    (run : compileFuel fuel optFuel n exp = some result) :
    result = ((compileSingSource n exp).1,
      appListAppend (compileSingSource n exp).2.1, (compileSingSource n exp).2.2) := by
  let larger := max fuel (expBudget exp + 1)
  have le : fuel ≤ larger := Nat.le_max_left _ _
  have bound : expBudget exp < larger := by dsimp [larger]; omega
  have stable := compileFuel_mono fuel larger optFuel n exp result le run
  have source := compileFuel_eq_source larger optFuel n exp bound
  rw [stable] at source
  exact Option.some.inj source

/-- The executed retry agrees with the source-shaped expression converter for
every initial fuel. This is Flapjack infrastructure, not pass correctness. -/
theorem compileBounded_eq_source (fuel optFuel n : Nat) (exp : Bvl.Exp) :
    compileBounded fuel optFuel n exp =
      some ((compileSingSource n exp).1,
        appListAppend (compileSingSource n exp).2.1, (compileSingSource n exp).2.2) := by
  cases run : compileFuel fuel optFuel n exp with
  | none =>
    have bound : expBudget exp < max fuel (expBudget exp + 1) := by omega
    simp [compileBounded, run, compileFuel_eq_source _ optFuel n exp bound]
  | some result =>
    have eq := compileFuel_success_eq_source fuel optFuel n exp result run
    simp [compileBounded, run, eq]

end Flapjack.Compiler.Backend.BvlToBvi
