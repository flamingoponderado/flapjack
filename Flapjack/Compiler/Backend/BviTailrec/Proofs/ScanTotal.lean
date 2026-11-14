module

public import Flapjack.Compiler.Backend.BviTailrec.Proofs.TermCorrespondence
public import Flapjack.Compiler.Backend.BviTailrec.Proofs.HasRecCorrespondence

@[expose] public section

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
      have ht := termBounded_eq fuel ctx (opType (fromOp op)) (.op op xs)
      cases checked <;> cases termResult : term ctx (opType (fromOp op)) (.op op xs) <;>
        simp [scanFuel, hc, ht, termResult] <;> repeat' (first | split | exact ⟨_, rfl⟩)
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

end Flapjack.Compiler.Backend.BviTailrec
