import Flapjack.Compiler.Backend.BviTailrec.Analysis

/-! Structural sufficiency for the tail-recursion type tests. These are
Flapjack infrastructure lemmas, not HOL correctness theorem ports. -/
namespace Flapjack.Compiler.Backend.BviTailrec
open Bvi

mutual
/-- Integer term analysis succeeds under a structural fuel bound. -/
theorem termIntFuel_succeeds (fuel : Nat) (ctx : List ValueType) (e : Exp)
    (bound : expBudget e < fuel) : ∃ result, termIntFuel fuel ctx e = some result := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases e with
    | op op xs =>
      cases xs with
      | nil => exact ⟨_, rfl⟩
      | cons x xs =>
        cases xs with
        | nil => exact ⟨_, rfl⟩
        | cons y xs =>
          cases xs with
          | nil =>
            have bx : expBudget x < fuel := by simp_all [expBudget, listBudget] <;> omega
            have by' : expBudget y < fuel := by simp_all [expBudget, listBudget] <;> omega
            obtain ⟨vx, hx⟩ := termIntFuel_succeeds fuel ctx x bx
            obtain ⟨vy, hy⟩ := termIntFuel_succeeds fuel ctx y by'
            cases vx <;> cases vy <;> simp [termIntFuel, hx, hy]
          | cons z zs => exact ⟨_, rfl⟩
    | _ => exact ⟨_, rfl⟩
termination_by fuel

/-- Arbitrary and list term analysis succeeds under a structural bound. -/
theorem termAnyFuel_succeeds (fuel : Nat) (ctx : List ValueType) (list : Bool) (e : Exp)
    (bound : expBudget e < fuel) : ∃ result, termAnyFuel fuel ctx list e = some result := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases e with
    | op op xs =>
      cases xs with
      | nil =>
        cases op <;> try exact ⟨_, rfl⟩
        case blockOp bop =>
          cases bop <;> try exact ⟨_, rfl⟩
          case cons tag => cases tag <;> exact ⟨_, rfl⟩
      | cons x xs =>
        cases xs with
        | nil => exact ⟨_, rfl⟩
        | cons y xs =>
          cases xs with
          | nil =>
            have bx : expBudget x < fuel := by simp_all [expBudget, listBudget] <;> omega
            have by' : expBudget y < fuel := by simp_all [expBudget, listBudget] <;> omega
            obtain ⟨xt, hxt⟩ := termAnyFuel_succeeds fuel ctx true x bx
            obtain ⟨yt, hyt⟩ := termAnyFuel_succeeds fuel ctx true y by'
            obtain ⟨yf, hyf⟩ := termAnyFuel_succeeds fuel ctx false y by'
            obtain ⟨xi, hxi⟩ := termIntFuel_succeeds fuel ctx x bx
            obtain ⟨yi, hyi⟩ := termIntFuel_succeeds fuel ctx y by'
            cases xt <;> cases xi <;> cases yt <;> cases yf <;> cases yi <;>
              cases list <;> simp [termAnyFuel, hxt, hyt, hyf, hxi, hyi] <;>
              split <;> simp_all <;> try (split <;> simp_all)
          | cons z zs => exact ⟨_, rfl⟩
    | _ => exact ⟨_, rfl⟩
termination_by fuel
end

/-- The executable term test cannot fail from traversal fuel. -/
theorem termBounded_succeeds (fuel : Nat) (ctx : List ValueType) (ty : ValueType) (e : Exp) :
    ∃ result, termBounded fuel ctx ty e = some result := by
  cases h : termFuel fuel ctx ty e with
  | some result => exact ⟨result, by simp [termBounded, h]⟩
  | none =>
    have bound : expBudget e < max fuel (expBudget e + 1) := by omega
    have done : ∃ result, termFuel (max fuel (expBudget e + 1)) ctx ty e = some result := by
      cases ty with
      | int => exact termIntFuel_succeeds _ ctx e bound
      | list => exact termAnyFuel_succeeds _ ctx true e bound
      | any => exact termAnyFuel_succeeds _ ctx false e bound
    obtain ⟨result, done⟩ := done
    exact ⟨result, by simp [termBounded, h, done]⟩

/-- Retrying a type test preserves any original successful result. -/
theorem termBounded_eq_of_success (fuel : Nat) (ctx : List ValueType) (ty : ValueType)
    (e : Exp) (result : Bool) (success : termFuel fuel ctx ty e = some result) :
    termBounded fuel ctx ty e = some result := by
  simp [termBounded, success]

/-- Candidate-operation checking cannot exhaust its term-analysis fuel. The
inner `none` remains the ordinary decision that no rewrite applies. -/
theorem checkOpFuel_succeeds (fuel : Nat) (ctx : List ValueType) (assoc : AssocOp)
    (loc : Nat) (xs : List Exp) : ∃ result, checkOpFuel fuel ctx assoc loc xs = some result := by
  cases xs with
  | nil => exact ⟨_, rfl⟩
  | cons x xs =>
    cases xs with
    | nil => exact ⟨_, rfl⟩
    | cons y xs =>
      cases xs with
      | nil =>
        obtain ⟨vx, hx⟩ := termBounded_succeeds fuel ctx (opType assoc) x
        obtain ⟨vy, hy⟩ := termBounded_succeeds fuel ctx (opType assoc) y
        simp only [checkOpFuel]
        split <;> simp [hx, hy] <;> repeat' (first | split | exact ⟨_, rfl⟩)
      | cons z zs => exact ⟨_, rfl⟩

end Flapjack.Compiler.Backend.BviTailrec
