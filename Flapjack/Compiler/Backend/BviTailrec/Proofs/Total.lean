import Flapjack.Compiler.Backend.BviTailrec.Rewrite
import Flapjack.Compiler.Backend.BviTailrec.Proofs.ScanTotal

/-! Structural sufficiency for the tail-recursion rewrite. These proofs do
not establish HOL correspondence or pass correctness. -/
namespace Flapjack.Compiler.Backend.BviTailrec
open Bvi

/-- Accumulator rewriting succeeds under a structural fuel bound. -/
theorem rewriteFuel_succeeds (fuel loc next : Nat) (op : AssocOp) (acc : Nat)
    (ctx : List ValueType) (e : Exp) (bound : expBudget e < fuel) :
    ∃ result, rewriteFuel fuel loc next op acc ctx e = some result := by
  induction fuel generalizing acc ctx e with
  | zero => omega
  | succ fuel ih =>
    cases e with
    | ifThenElse cond yes no =>
      have by' : expBudget yes < fuel := by simp_all [expBudget] <;> omega
      have bn : expBudget no < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨ctx', ty, rec, assoc⟩, hc⟩ := scanBounded_succeeds fuel ctx loc cond
      obtain ⟨⟨ry, y⟩, hy⟩ := ih acc ctx' yes by'
      obtain ⟨⟨rn, n⟩, hn⟩ := ih acc ctx' no bn
      exact ⟨_, by simp [rewriteFuel, hc, hy, hn]; rfl⟩
    | «let» xs body =>
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨scans, hs⟩ := scanListBounded_succeeds fuel ctx loc xs
      let types := scans.map fun (_, ty, _, _) => ty
      let last := match scans.getLast? with | some (cs, _, _, _) => cs | none => ctx
      obtain ⟨⟨r, body'⟩, hb⟩ := ih (acc + xs.length) (types ++ last) body bb
      refine ⟨(r, .let xs body'), ?_⟩
      simp only [rewriteFuel, hs]
      change (rewriteFuel fuel loc next op (acc + xs.length) (types ++ last) body).bind
        (fun (result : Bool × Exp) => some (result.1, Exp.let xs result.2)) = _
      rw [hb]
      rfl
    | tick x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨r, x'⟩, hx⟩ := ih acc ctx x bx
      exact ⟨_, by simp [rewriteFuel, hx]; rfl⟩
    | op actual xs =>
      obtain ⟨checked, hc⟩ := checkOpFuel_succeeds fuel ctx op loc xs
      cases checked <;> simp [rewriteFuel, hc] <;> repeat' split
      all_goals simp_all
    | _ => exact ⟨_, rfl⟩

/-- A structurally sufficient budget makes the expression rewrite succeed.
The inner `none` remains the ordinary no-rewrite decision. -/
theorem compileExpFuel_succeeds (fuel loc next arity : Nat) (e : Exp)
    (bound : expBudget e < fuel) : ∃ result, compileExpFuel fuel loc next arity e = some result := by
  obtain ⟨decision, hd⟩ := checkExpFuel_succeeds fuel loc arity e
  cases decision with
  | none => exact ⟨_, by simp [compileExpFuel, hd]; rfl⟩
  | some op =>
    obtain ⟨⟨changed, worker⟩, hw⟩ :=
      rewriteFuel_succeeds fuel loc next op arity (List.replicate arity .any) e bound
    exact ⟨_, by simp [compileExpFuel, hd, hw]; rfl⟩

/-- The production rewrite retry cannot fail from traversal fuel. -/
theorem compileExpBounded_succeeds (fuel loc next arity : Nat) (e : Exp) :
    ∃ result, compileExpBounded fuel loc next arity e = some result := by
  cases h : compileExpFuel fuel loc next arity e with
  | some result => exact ⟨result, by simp [compileExpBounded, h]⟩
  | none =>
    have bound : expBudget e < max fuel (expBudget e + 1) := by omega
    obtain ⟨result, done⟩ := compileExpFuel_succeeds (max fuel (expBudget e + 1)) loc next arity e bound
    exact ⟨result, by simp [compileExpBounded, h, done]⟩

/-- Previously successful rewrite results are unchanged by the retry. -/
theorem compileExpBounded_eq_of_success (fuel loc next arity : Nat) (e : Exp)
    (result : Option (Exp × Exp)) (success : compileExpFuel fuel loc next arity e = some result) :
    compileExpBounded fuel loc next arity e = some result := by
  simp [compileExpBounded, success]

/-- Processing all functions cannot fail from traversal fuel. -/
theorem compileEachFuel_succeeds (fuel next : Nat) (code : List (Nat × Nat × Exp)) :
    ∃ result, compileEachFuel fuel next code = some result := by
  induction code generalizing next with
  | nil => exact ⟨_, rfl⟩
  | cons p ps ih =>
    obtain ⟨loc, arity, body⟩ := p
    obtain ⟨decision, hd⟩ := compileExpBounded_succeeds fuel loc next arity body
    cases decision with
    | none =>
      obtain ⟨⟨next', rest⟩, hr⟩ := ih next
      exact ⟨_, by simp [compileEachFuel, hd, hr]; rfl⟩
    | some pair =>
      obtain ⟨wrapper, worker⟩ := pair
      obtain ⟨⟨next', rest⟩, hr⟩ := ih (next + Flapjack.bvlToBviNamespaces)
      exact ⟨_, by simp [compileEachFuel, hd, hr]; rfl⟩

/-- Whole-program tail-recursion conversion cannot exhaust its traversal
budgets. This is not the HOL pass-correctness theorem. -/
theorem compileProgFuel_succeeds (fuel : Nat) (enabled : Bool) (next : Nat)
    (code : List (Nat × Nat × Exp)) :
    ∃ result, compileProgFuel fuel enabled next code = some result := by
  cases enabled with
  | false => exact ⟨_, rfl⟩
  | true =>
    obtain ⟨result, h⟩ := compileEachFuel_succeeds fuel next code
    exact ⟨result, by simpa [compileProgFuel] using h⟩

end Flapjack.Compiler.Backend.BviTailrec
