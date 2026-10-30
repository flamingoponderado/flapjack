import Flapjack.Compiler.Backend.BviTmc.Proofs.PureTotal

/-! Structural sufficiency for TMC constructor extraction. These are
Flapjack infrastructure lemmas, not HOL pass-correctness ports. -/
namespace Flapjack.Compiler.Backend.BviTmc
open Bvi

private theorem pureBranch_succeeds (fuel n : Nat) (e : Exp) :
    ∃ result : Option (List Exp × Sum (List Nat) CallBlock), (do
      let yes ← pureBounded fuel n e
      if yes then pure (some ([e], Sum.inl [0])) else pure none) = some result := by
  obtain ⟨yes, h⟩ := pureBounded_succeeds fuel n e
  cases yes <;> exact ⟨_, by simp [h]; rfl⟩

mutual
/-- Extracting one expression succeeds under a structural fuel bound. -/
theorem extractOneFuel_succeeds (fuel n loc tag : Nat) (e : Exp)
    (bound : expBudget e < fuel) : ∃ result, extractOneFuel fuel n loc tag e = some result := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases e with
    | call ticks dest args handler =>
      simp only [extractOneFuel]
      split <;> exact ⟨_, rfl⟩
    | op op xs =>
      cases op with
      | blockOp bop =>
        cases bop with
        | cons childTag =>
          have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
          obtain ⟨out, hout⟩ := extractListFuel_succeeds fuel n loc childTag xs bx
          obtain ⟨value, hv⟩ := pureBounded_succeeds fuel n (.op (.blockOp (.cons childTag)) xs)
          cases out with
          | none => exact ⟨_, by simp [extractOneFuel, hout]; rfl⟩
          | some item =>
            obtain ⟨bs, kind⟩ := item
            cases kind with
            | inl vs => cases value <;> exact ⟨_, by simp [extractOneFuel, hout, hv]; rfl⟩
            | inr cb => exact ⟨_, by simp [extractOneFuel, hout]; rfl⟩
        | _ =>
          simp only [extractOneFuel]
          apply pureBranch_succeeds
      | _ =>
        simp only [extractOneFuel]
        apply pureBranch_succeeds
    | _ =>
      simp only [extractOneFuel]
      apply pureBranch_succeeds
termination_by fuel

/-- Extracting an operand list succeeds under its structural fuel bound. -/
theorem extractListFuel_succeeds (fuel n loc tag : Nat) (xs : List Exp)
    (bound : listBudget xs < fuel) : ∃ result, extractListFuel fuel n loc tag xs = some result := by
  cases xs with
  | nil => exact ⟨_, rfl⟩
  | cons x xs =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have bx : expBudget x < fuel := by simp_all [listBudget] <;> omega
      obtain ⟨one, hone⟩ := extractOneFuel_succeeds fuel n loc tag x bx
      cases xs with
      | nil => exact ⟨_, by simp [extractListFuel, hone]; rfl⟩
      | cons y ys =>
        have br : listBudget (y :: ys) < fuel := by simp_all [listBudget] <;> omega
        obtain ⟨rest, hrest⟩ := extractListFuel_succeeds fuel n loc tag (y :: ys) br
        simp only [extractListFuel, hrest]
        cases rest with
        | none => exact ⟨_, rfl⟩
        | some item =>
          obtain ⟨bs, kind⟩ := item
          cases kind with
          | inl vs =>
            rw [hone]
            cases one with
            | none => exact ⟨_, rfl⟩
            | some item =>
              obtain ⟨bs', kind'⟩ := item
              cases kind' with
              | inl vs' => simp; split <;> exact ⟨_, rfl⟩
              | inr cb => cases cb <;> simp <;> repeat' (first | split | exact ⟨_, rfl⟩)
          | inr cb => cases h : shiftBlock 1 cb <;> simp [h] <;> exact ⟨_, rfl⟩
termination_by fuel
end

/-- The executable extraction wrapper cannot fail due to traversal fuel. -/
theorem extractListBounded_succeeds (fuel n loc tag : Nat) (xs : List Exp) :
    ∃ result, extractListBounded fuel n loc tag xs = some result := by
  cases h : extractListFuel fuel n loc tag xs with
  | some result => exact ⟨result, by simp [extractListBounded, h]⟩
  | none =>
    have bound : listBudget xs < max fuel (listBudget xs + 1) := by omega
    obtain ⟨result, done⟩ := extractListFuel_succeeds (max fuel (listBudget xs + 1)) n loc tag xs bound
    exact ⟨result, by simp [extractListBounded, h, done]⟩

/-- The retry preserves every result from the original extraction budget. -/
theorem extractListBounded_eq_of_success (fuel n loc tag : Nat) (xs : List Exp)
    (result : Option (List Exp × Sum (List Nat) CallBlock))
    (success : extractListFuel fuel n loc tag xs = some result) :
    extractListBounded fuel n loc tag xs = some result := by
  simp [extractListBounded, success]

/-- Constructor-block extraction cannot fail from traversal fuel. The inner
`none` still represents an expression that does not match the optimization. -/
theorem toBlockFuel_succeeds (fuel n loc : Nat) (e : Exp) :
    ∃ result, toBlockFuel fuel n loc e = some result := by
  cases e with
  | op op xs =>
    cases op with
    | blockOp bop =>
      cases bop with
      | cons tag =>
        obtain ⟨out, h⟩ := extractListBounded_succeeds fuel n loc tag xs
        cases out with
        | none => exact ⟨_, by simp [toBlockFuel, h]; rfl⟩
        | some item =>
          obtain ⟨bs, kind⟩ := item
          cases kind <;> exact ⟨_, by simp [toBlockFuel, h]; rfl⟩
      | _ => exact ⟨_, rfl⟩
    | _ => exact ⟨_, rfl⟩
  | _ => exact ⟨_, rfl⟩

end Flapjack.Compiler.Backend.BviTmc
