import Flapjack.Compiler.Backend.BviTailrec.Proofs.TermTotal
import Flapjack.Compiler.Backend.BviTailrec.Proofs.HasRecTotal

/-! Structural sufficiency of the tail-recursion scan. These are Flapjack
infrastructure lemmas; HOL correspondence is a separate obligation. -/
namespace Flapjack.Compiler.Backend.BviTailrec
open Bvi

mutual
/-- Scanning one expression succeeds under a structural fuel bound. -/
theorem scanFuel_succeeds (fuel : Nat) (ctx : List ValueType) (loc : Nat) (e : Exp)
    (bound : expBudget e < fuel) : ∃ result, scanFuel fuel ctx loc e = some result := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases e with
    | ifThenElse cond yes no =>
      have bc : expBudget cond < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget yes < fuel := by simp_all [expBudget] <;> omega
      have bn : expBudget no < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨ci, ti, ri, oi⟩, hc⟩ := scanFuel_succeeds fuel ctx loc cond bc
      obtain ⟨⟨ct, tt, rt, ot⟩, ht⟩ := scanFuel_succeeds fuel ci loc yes by'
      obtain ⟨⟨ce, te, re, oe⟩, he⟩ := scanFuel_succeeds fuel ci loc no bn
      exact ⟨_, by simp [scanFuel, hc, ht, he]; rfl⟩
    | «let» xs body =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨scans, hs⟩ := scanListFuel_succeeds fuel ctx loc xs bx
      let types := scans.map fun (_, ty, _, _) => ty
      let last := match scans.getLast? with | some (cs, _, _, _) => cs | none => ctx
      obtain ⟨⟨out, ty, r, op⟩, hb⟩ := scanFuel_succeeds fuel (types ++ last) loc body bb
      refine ⟨(out.drop scans.length, ty, false, op), ?_⟩
      simp only [scanFuel, hs]
      change (scanFuel fuel (types ++ last) loc body).bind
        (fun s => some (s.1.drop scans.length, s.2.1, false, s.2.2.2)) = _
      rw [hb]
      rfl
    | tick x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨out, h⟩ := scanFuel_succeeds fuel ctx loc x bx
      exact ⟨_, by simp [scanFuel, h]; rfl⟩
    | op op xs =>
      obtain ⟨checked, hc⟩ := checkOpFuel_succeeds fuel ctx (fromOp op) loc xs
      obtain ⟨term, ht⟩ := termBounded_succeeds fuel ctx (opType (fromOp op)) (.op op xs)
      cases checked <;> cases term <;>
        simp [scanFuel, hc, ht] <;> repeat' (first | split | exact ⟨_, rfl⟩)
      all_goals simp_all
    | _ => exact ⟨_, rfl⟩
termination_by fuel

/-- Scanning an operand list succeeds under its structural fuel bound. -/
theorem scanListFuel_succeeds (fuel : Nat) (ctx : List ValueType) (loc : Nat) (xs : List Exp)
    (bound : listBudget xs < fuel) : ∃ result, scanListFuel fuel ctx loc xs = some result := by
  cases xs with
  | nil => cases fuel <;> exact ⟨_, rfl⟩
  | cons x xs =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have bx : expBudget x < fuel := by simp_all [listBudget] <;> omega
      have bxs : listBudget xs < fuel := by simp_all [listBudget] <;> omega
      obtain ⟨⟨next, ty, rec, op⟩, hx⟩ := scanFuel_succeeds fuel ctx loc x bx
      obtain ⟨rest, hr⟩ := scanListFuel_succeeds fuel next loc xs bxs
      exact ⟨_, by simp [scanListFuel, hx, hr]; rfl⟩
termination_by fuel
end

/-- The executable scan cannot exhaust traversal fuel. -/
theorem scanBounded_succeeds (fuel : Nat) (ctx : List ValueType) (loc : Nat) (e : Exp) :
    ∃ result, scanBounded fuel ctx loc e = some result := by
  cases h : scanFuel fuel ctx loc e with
  | some result => exact ⟨result, by simp [scanBounded, h]⟩
  | none =>
    have bound : expBudget e < max fuel (expBudget e + 1) := by omega
    obtain ⟨result, done⟩ := scanFuel_succeeds (max fuel (expBudget e + 1)) ctx loc e bound
    exact ⟨result, by simp [scanBounded, h, done]⟩

/-- The executable operand scan cannot exhaust traversal fuel. -/
theorem scanListBounded_succeeds (fuel : Nat) (ctx : List ValueType) (loc : Nat) (xs : List Exp) :
    ∃ result, scanListBounded fuel ctx loc xs = some result := by
  cases h : scanListFuel fuel ctx loc xs with
  | some result => exact ⟨result, by simp [scanListBounded, h]⟩
  | none =>
    have bound : listBudget xs < max fuel (listBudget xs + 1) := by omega
    obtain ⟨result, done⟩ := scanListFuel_succeeds (max fuel (listBudget xs + 1)) ctx loc xs bound
    exact ⟨result, by simp [scanListBounded, h, done]⟩

/-- The scan retry preserves each result obtained using the original fuel. -/
theorem scanBounded_eq_of_success (fuel : Nat) (ctx : List ValueType) (loc : Nat) (e : Exp)
    (result : List ValueType × ValueType × Bool × Option AssocOp)
    (success : scanFuel fuel ctx loc e = some result) : scanBounded fuel ctx loc e = some result := by
  simp [scanBounded, success]

/-- The list-scan retry preserves each result obtained using the original fuel. -/
theorem scanListBounded_eq_of_success (fuel : Nat) (ctx : List ValueType) (loc : Nat) (xs : List Exp)
    (result : List (List ValueType × ValueType × Bool × Option AssocOp))
    (success : scanListFuel fuel ctx loc xs = some result) :
    scanListBounded fuel ctx loc xs = some result := by
  simp [scanListBounded, success]

/-- Checking whether to optimize an expression cannot fail from scan fuel.
The inner `none` is the ordinary decision not to rewrite. -/
theorem checkExpFuel_succeeds (fuel loc arity : Nat) (e : Exp) :
    ∃ result, checkExpFuel fuel loc arity e = some result := by
  obtain ⟨isRec, hr⟩ := hasRecBounded_succeeds fuel loc e
  cases isRec with
  | false => exact ⟨_, by simp [checkExpFuel, hr]; rfl⟩
  | true =>
    obtain ⟨⟨ctx, ty, rec, op⟩, hs⟩ := scanBounded_succeeds fuel (List.replicate arity .any) loc e
    cases op <;> simp [checkExpFuel, hr, hs] <;> repeat' (first | split | exact ⟨_, rfl⟩)

end Flapjack.Compiler.Backend.BviTailrec
