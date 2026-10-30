import Flapjack.Compiler.Backend.BvlToBvi.Compile

/-! Stability of successful BVL-to-BVI traversals under additional fuel. -/
namespace Flapjack.Compiler.Backend.BvlToBvi

mutual
/-- Increasing expression-traversal fuel preserves every successful result.
This is Flapjack infrastructure, not a source correctness theorem. -/
theorem compileFuel_succ_of_success (fuel optFuel n : Nat) (exp : Bvl.Exp)
    (result : Bvi.Exp × List (Nat × Nat × Bvi.Exp) × Nat)
    (run : compileFuel fuel optFuel n exp = some result) :
    compileFuel (fuel + 1) optFuel n exp = some result := by
  cases fuel with
  | zero => simp [compileFuel] at run
  | succ fuel =>
    cases exp with
    | var v => simpa [compileFuel] using run
    | force loc v => simpa [compileFuel] using run
    | raise x =>
      cases hx : compileFuel fuel optFuel n x with
      | none => simp [compileFuel, hx] at run
      | some out =>
        have hx' := compileFuel_succ_of_success fuel optFuel n x out hx
        rcases out with ⟨x', aux, next⟩
        rw [compileFuel, hx] at run
        rw [compileFuel, hx']
        simpa using run
    | tick x =>
      cases hx : compileFuel fuel optFuel n x with
      | none => simp [compileFuel, hx] at run
      | some out =>
        have hx' := compileFuel_succ_of_success fuel optFuel n x out hx
        rcases out with ⟨x', aux, next⟩
        rw [compileFuel, hx] at run
        rw [compileFuel, hx']
        simpa using run
    | ifThenElse x y z =>
      cases hx : compileFuel fuel optFuel n x with
      | none => simp [compileFuel, hx] at run
      | some out =>
        have hx' := compileFuel_succ_of_success fuel optFuel n x out hx
        rcases out with ⟨x', a, n1⟩
        cases hy : compileFuel fuel optFuel n1 y with
        | none => simp [compileFuel, hx, hy] at run
        | some out =>
          have hy' := compileFuel_succ_of_success fuel optFuel n1 y out hy
          rcases out with ⟨y', b, n2⟩
          cases hz : compileFuel fuel optFuel n2 z with
          | none => simp [compileFuel, hx, hy, hz] at run
          | some out =>
            have hz' := compileFuel_succ_of_success fuel optFuel n2 z out hz
            rcases out with ⟨z', c, n3⟩
            rw [compileFuel, hx] at run
            simp only [bind, Option.bind] at run
            rw [hy] at run
            dsimp only at run
            rw [hz] at run
            rw [compileFuel, hx']
            simp only [bind, Option.bind]
            rw [hy']
            dsimp only
            rw [hz']
            simpa using run
    | op op xs =>
      cases ha : compileListFuel fuel optFuel n xs with
      | none => simp [compileFuel, ha] at run
      | some out =>
        have ha' := compileListFuel_succ_of_success fuel optFuel n xs out ha
        rcases out with ⟨xs', aux, next⟩
        rw [compileFuel, ha] at run
        rw [compileFuel, ha']
        simpa using run
    | call ticks dest xs =>
      cases ha : compileListFuel fuel optFuel n xs with
      | none => simp [compileFuel, ha] at run
      | some out =>
        have ha' := compileListFuel_succ_of_success fuel optFuel n xs out ha
        rcases out with ⟨xs', aux, next⟩
        rw [compileFuel, ha] at run
        rw [compileFuel, ha']
        simpa using run
    | «let» xs body =>
      cases xs with
      | nil =>
        let args := (destLet body).1
        let inner := (destLet body).2
        have dest : destLet body = (args, inner) := by simp [args, inner]
        cases ha : compileListFuel fuel optFuel n args with
        | none => simp [compileFuel, dest, ha] at run
        | some out =>
          have ha' := compileListFuel_succ_of_success fuel optFuel n args out ha
          rcases out with ⟨args', a, n1⟩
          cases hb : compileFuel fuel optFuel n1 inner with
          | none => simp [compileFuel, dest, ha, hb] at run
          | some out =>
            have hb' := compileFuel_succ_of_success fuel optFuel n1 inner out hb
            rcases out with ⟨inner', b, n2⟩
            rw [compileFuel, dest] at run
            simp only [List.isEmpty_nil, ↓reduceIte, ha, bind, Option.bind] at run
            rw [hb] at run
            rw [compileFuel, dest]
            simp only [List.isEmpty_nil, ↓reduceIte, ha', bind, Option.bind]
            rw [hb']
            simpa using run
      | cons x xs =>
        cases ha : compileListFuel fuel optFuel n (x :: xs) with
        | none => simp [compileFuel, ha] at run
        | some out =>
          have ha' := compileListFuel_succ_of_success fuel optFuel n (x :: xs) out ha
          rcases out with ⟨args, a, n1⟩
          cases hb : compileFuel fuel optFuel n1 body with
          | none => simp [compileFuel, ha, hb] at run
          | some out =>
            have hb' := compileFuel_succ_of_success fuel optFuel n1 body out hb
            rcases out with ⟨body', b, n2⟩
            rw [compileFuel] at run
            simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, ha, bind, Option.bind] at run
            rw [hb] at run
            rw [compileFuel]
            simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, ha', bind, Option.bind]
            rw [hb']
            simpa using run
    | handle x y =>
      let args := (destLet x).1
      let inner := (destLet x).2
      have dest : destLet x = (args, inner) := by simp [args, inner]
      cases ha : compileListFuel fuel optFuel n args with
      | none => simp [compileFuel, dest, ha] at run
      | some out =>
        have ha' := compileListFuel_succ_of_success fuel optFuel n args out ha
        rcases out with ⟨args', a, n1⟩
        cases hb : compileFuel fuel optFuel n1 inner with
        | none => simp [compileFuel, dest, ha, hb] at run
        | some out =>
          have hb' := compileFuel_succ_of_success fuel optFuel n1 inner out hb
          rcases out with ⟨inner', b, n2⟩
          cases hc : compileFuel fuel optFuel n2 y with
          | none => simp [compileFuel, dest, ha, hb, hc] at run
          | some out =>
            have hc' := compileFuel_succ_of_success fuel optFuel n2 y out hc
            rcases out with ⟨handler, c, n3⟩
            rw [compileFuel, dest] at run
            dsimp only at run
            rw [ha] at run
            simp only [bind, Option.bind] at run
            rw [hb] at run
            dsimp only at run
            rw [hc] at run
            rw [compileFuel, dest]
            dsimp only
            rw [ha']
            simp only [bind, Option.bind]
            rw [hb']
            dsimp only
            rw [hc']
            simpa using run
termination_by fuel

/-- Increasing list-traversal fuel preserves every successful result. -/
theorem compileListFuel_succ_of_success (fuel optFuel n : Nat) (xs : List Bvl.Exp)
    (result : List Bvi.Exp × List (Nat × Nat × Bvi.Exp) × Nat)
    (run : compileListFuel fuel optFuel n xs = some result) :
    compileListFuel (fuel + 1) optFuel n xs = some result := by
  cases fuel with
  | zero => simp [compileListFuel] at run
  | succ fuel =>
    cases xs with
    | nil => simpa [compileListFuel] using run
    | cons x xs =>
      cases hx : compileFuel fuel optFuel n x with
      | none => simp [compileListFuel, hx] at run
      | some out =>
        have hx' := compileFuel_succ_of_success fuel optFuel n x out hx
        rcases out with ⟨x', a, n1⟩
        cases ht : compileListFuel fuel optFuel n1 xs with
        | none => simp [compileListFuel, hx, ht] at run
        | some tail =>
          have ht' := compileListFuel_succ_of_success fuel optFuel n1 xs tail ht
          rcases tail with ⟨xs', b, n2⟩
          rw [compileListFuel, hx] at run
          simp only [bind, Option.bind] at run
          rw [ht] at run
          rw [compileListFuel, hx']
          simp only [bind, Option.bind]
          rw [ht']
          simpa using run
termination_by fuel
end

/-- A successful expression traversal is stable at every greater fuel. -/
theorem compileFuel_mono (fuel larger optFuel n : Nat) (exp : Bvl.Exp)
    (result : Bvi.Exp × List (Nat × Nat × Bvi.Exp) × Nat)
    (le : fuel ≤ larger) (run : compileFuel fuel optFuel n exp = some result) :
    compileFuel larger optFuel n exp = some result := by
  induction le with
  | refl => exact run
  | @step larger _ ih => exact compileFuel_succ_of_success larger optFuel n exp result ih

end Flapjack.Compiler.Backend.BvlToBvi
