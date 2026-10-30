import Flapjack.Compiler.Backend.BvlInline.Small

/-! Correspondence between the executable and total BVL size traversals. -/
namespace Flapjack.Compiler.Backend.BvlInline
open Bvl

private def Agrees (actual : Option Nat) (expected : Nat) : Prop :=
  ∀ result, actual = some result → result = expected

private theorem agreesSome (n : Nat) : Agrees (some n) n := by
  intro result h
  exact (Option.some.inj h).symm

private theorem agreesNone (n : Nat) : Agrees none n := by
  intro result h
  cases h

private theorem agreesStep (actual : Option Nat) (expected : Nat)
    (next : Nat → Option Nat) (spec : Nat → Nat)
    (first : Agrees actual expected) (rest : ∀ n, Agrees (next n) (spec n)) :
    Agrees (do let n ← actual; if n == 0 then pure 0 else next n)
      (if expected = 0 then 0 else spec expected) := by
  cases eq : actual with
  | none => simp [agreesNone]
  | some value =>
    have same := first value eq
    subst value
    by_cases zero : expected = 0
    · simp [zero, agreesSome]
    · simpa [zero] using rest expected

private theorem zeroChoice (n other : Nat) : (if n = 0 then n else other) =
    (if n = 0 then 0 else other) := by
  by_cases zero : n = 0 <;> simp [zero]

private theorem zeroChoiceSome (n : Nat) (other : Option Nat) :
    (if n = 0 then some n else other) = (if n = 0 then some 0 else other) := by
  by_cases zero : n = 0 <;> simp [zero]

private theorem smallFuel_agrees (fuel : Nat) :
    (∀ n e, Agrees (smallExpFuel fuel n e) (isSmallSing n e)) ∧
    (∀ n xs, Agrees (smallListFuel fuel n xs) (isSmallList n xs)) := by
  induction fuel with
  | zero =>
    constructor
    · intro n e; exact agreesNone _
    · intro n xs
      cases xs with
      | nil => simpa [smallListFuel, isSmallList] using agreesSome n
      | cons x xs => simpa [smallListFuel] using agreesNone (isSmallList n (x :: xs))
  | succ fuel ih =>
    constructor
    · intro n e
      cases e with
      | var v => simpa [smallExpFuel, isSmallSing] using agreesSome n
      | force a b => simpa [smallExpFuel, isSmallSing] using agreesSome n
      | tick e => simpa [smallExpFuel, isSmallSing] using ih.1 n e
      | raise e =>
        by_cases zero : n - 1 = 0
        · simpa [smallExpFuel, isSmallSing, zero] using agreesSome 0
        · simpa [smallExpFuel, isSmallSing, zero] using ih.1 (n - 1) e
      | op op xs =>
        by_cases zero : n - 1 = 0
        · simpa [smallExpFuel, isSmallSing, zero] using agreesSome 0
        · simpa [smallExpFuel, isSmallSing, zero] using ih.2 (n - 1) xs
      | call ticks dest xs =>
        by_cases zero : n - 1 = 0
        · simpa [smallExpFuel, isSmallSing, zero] using agreesSome 0
        · simpa [smallExpFuel, isSmallSing, zero] using ih.2 (n - 1) xs
      | handle x y =>
        by_cases zero : n - 1 = 0
        · simpa [smallExpFuel, isSmallSing, zero] using agreesSome 0
        · simpa [smallExpFuel, isSmallSing, zero] using
            agreesStep (smallExpFuel fuel (n - 1) x) (isSmallSing (n - 1) x)
              (fun n => smallExpFuel fuel n y) (fun n => isSmallSing n y)
              (ih.1 (n - 1) x) (fun n => ih.1 n y)
      | «let» xs body =>
        by_cases zero : n - 1 = 0
        · simpa [smallExpFuel, isSmallSing, zero] using agreesSome 0
        · simpa [smallExpFuel, isSmallSing, zero] using
            agreesStep (smallListFuel fuel (n - 1) xs) (isSmallList (n - 1) xs)
              (fun n => smallExpFuel fuel n body) (fun n => isSmallSing n body)
              (ih.2 (n - 1) xs) (fun n => ih.1 n body)
      | ifThenElse x y z =>
        by_cases zero : n - 1 = 0
        · simpa [smallExpFuel, isSmallSing, zero] using agreesSome 0
        · simpa [smallExpFuel, isSmallSing, zero] using
            agreesStep (smallExpFuel fuel (n - 1) x) (isSmallSing (n - 1) x)
              (fun n => do let n ← smallExpFuel fuel n y; if n == 0 then pure 0 else smallExpFuel fuel n z)
              (fun n => if isSmallSing n y = 0 then 0 else isSmallSing (isSmallSing n y) z)
              (ih.1 (n - 1) x) (fun n => agreesStep _ _ _ _ (ih.1 n y) (fun n => ih.1 n z))
    · intro n xs
      cases xs with
      | nil => simpa [smallListFuel, isSmallList] using agreesSome n
      | cons x xs =>
        by_cases zero : n = 0
        · subst n; simpa [smallListFuel, isSmallList] using agreesSome 0
        · simpa [smallListFuel, isSmallList, zero, zeroChoice, zeroChoiceSome] using
            agreesStep (smallExpFuel fuel n x) (isSmallSing n x)
              (fun n => smallListFuel fuel n xs) (fun n => isSmallList n xs)
              (ih.1 n x) (fun n => ih.2 n xs)

/-- Every successful bounded traversal returns the source size budget. This
executable correspondence has no standalone HOL declaration. -/
theorem smallExpFuel_eq (fuel n : Nat) (e : Exp) (result : Nat)
    (run : smallExpFuel fuel n e = some result) : result = isSmallSing n e :=
  (smallFuel_agrees fuel).1 n e result run

/-- The production retry returns the original size-budget result for every
input. This executable correspondence has no standalone HOL declaration. -/
theorem smallExpBounded_eq (fuel n : Nat) (e : Exp) :
    smallExpBounded fuel n e = some (isSmallSing n e) := by
  cases first : smallExpFuel fuel n e with
  | some result =>
    have correct := smallExpFuel_eq fuel n e result first
    simp [smallExpBounded, first, correct]
  | none =>
    have bound : BvlToBvi.expBudget e < max fuel (BvlToBvi.expBudget e + 1) := by omega
    obtain ⟨result, run⟩ := smallExpFuel_succeeds _ n e bound
    have correct := smallExpFuel_eq _ n e result run
    simp [smallExpBounded, first, run, correct]

end Flapjack.Compiler.Backend.BvlInline
