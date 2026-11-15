module

public import Flapjack.Misc.Option.MapM
public import Flapjack.Compiler.Backend.BvlHandle.Proofs.HelpersProduction
public import Flapjack.Compiler.Backend.ListFoldTotal

@[expose] public section

/-! Structural sufficiency for handler simplification. These results are
Flapjack infrastructure, not HOL pass-correctness ports. -/
namespace Flapjack.Compiler.Backend.BvlHandle
open Bvl BvlToBvi

/-- The executable short-circuit fold computes the source list raise test. -/
theorem foldRaiseBounded_eq (fuel : Nat) (xs : List Exp) (init : Bool) :
    xs.foldlM (fun b e => if b then pure true else canRaiseBounded fuel e) init =
      some (init || canRaiseList xs) := by
  induction xs generalizing init with
  | nil => cases init <;> simp [canRaiseList]
  | cons e es ih =>
    simp only [canRaiseBounded_eq] at ih ⊢
    cases init with
    | true =>
      simp only [List.foldlM_cons, ↓reduceIte, bind, Option.bind]
      simpa [canRaiseList] using ih true
    | false =>
      simp only [List.foldlM_cons, Bool.false_eq_true, ↓reduceIte,
        bind, Option.bind]
      simpa [canRaiseList] using ih (canRaise e)

mutual
/-- Handler simplification succeeds under a structural fuel bound. -/
theorem simplifyFuel_succeeds (fuel : Nat) (e : Exp) (bound : expBudget e < fuel) :
    ∃ result, simplifyFuel fuel e = some result := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases e with
    | var v => exact ⟨_, rfl⟩
    | force loc v => exact ⟨_, rfl⟩
    | ifThenElse x y z =>
      have bx : expBudget x < fuel := by simp_all [expBudget]; omega
      have by' : expBudget y < fuel := by simp_all [expBudget]; omega
      have bz : expBudget z < fuel := by simp_all [expBudget]; omega
      obtain ⟨x', hx⟩ := simplifyFuel_succeeds fuel x bx
      obtain ⟨y', hy⟩ := simplifyFuel_succeeds fuel y by'
      obtain ⟨z', hz⟩ := simplifyFuel_succeeds fuel z bz
      exact ⟨_, by simp [simplifyFuel, hx, hy, hz]; rfl⟩
    | «let» xs body =>
      have bx : listBudget xs < fuel := by simp_all [expBudget]; omega
      have bb : expBudget body < fuel := by simp_all [expBudget]; omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (simplifyFuel fuel) (by
        intro x hx; apply simplifyFuel_succeeds; have := member_budget_lt xs x hx; omega)
      obtain ⟨body', hb⟩ := simplifyFuel_succeeds fuel body bb
      exact ⟨_, by simp [simplifyFuel, hy, hb]; rfl⟩
    | handle x handler =>
      have bh : expBudget x + expBudget handler + 1 < fuel := by simp_all [expBudget]; omega
      obtain ⟨result, h⟩ := makeHandleFuel_succeeds fuel x handler 0 bh
      exact ⟨_, by simpa [simplifyFuel] using h⟩
    | raise x =>
      have bx : expBudget x < fuel := by simp_all [expBudget]; omega
      obtain ⟨x', hx⟩ := simplifyFuel_succeeds fuel x bx
      exact ⟨_, by simp [simplifyFuel, hx]; rfl⟩
    | tick x =>
      have bx : expBudget x < fuel := by simp_all [expBudget]; omega
      obtain ⟨x', hx⟩ := simplifyFuel_succeeds fuel x bx
      exact ⟨_, by simp [simplifyFuel, hx]; rfl⟩
    | op op xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget]; omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (simplifyFuel fuel) (by
        intro x hx; apply simplifyFuel_succeeds; have := member_budget_lt xs x hx; omega)
      exact ⟨_, by simp [simplifyFuel, hy]; rfl⟩
    | call ticks dest xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget]; omega
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (simplifyFuel fuel) (by
        intro x hx; apply simplifyFuel_succeeds; have := member_budget_lt xs x hx; omega)
      exact ⟨_, by simp [simplifyFuel, hy]; rfl⟩
termination_by fuel

/-- Moving a handler succeeds when fuel covers both input expressions. -/
theorem makeHandleFuel_succeeds (fuel : Nat) (x handler : Exp) (depth : Nat)
    (bound : expBudget x + expBudget handler + 1 < fuel) :
    ∃ result, makeHandleFuel fuel x handler depth = some result := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    have bx : expBudget x < fuel := by omega
    have bh : expBudget handler < fuel := by omega
    obtain ⟨x', hx⟩ := simplifyFuel_succeeds fuel x bx
    obtain ⟨handler', hh⟩ := simplifyFuel_succeeds fuel handler bh
    have ha := adjustVarsBounded_eq fuel 1 depth handler'
    cases x with
    | raise r =>
      cases hr : canRaise r <;>
        exact ⟨_, by simp [makeHandleFuel, hx, hh, ha, canRaiseBounded_eq, hr]; rfl⟩
    | «let» xs body =>
      have bb : expBudget body + expBudget handler + 1 < fuel := by simp_all [expBudget]; omega
      have bl : listBudget xs < fuel := by simp_all [expBudget]; omega
      have hr := foldRaiseBounded_eq fuel xs false
      simp only [Bool.false_or, Option.pure_def] at hr
      obtain ⟨ys, hy⟩ := mapM_succeeds xs (simplifyFuel fuel) (by
        intro e he; apply simplifyFuel_succeeds; have := member_budget_lt xs e he; omega)
      obtain ⟨body', hbody⟩ := makeHandleFuel_succeeds fuel body handler (depth + xs.length) bb
      cases raises : canRaiseList xs <;> exact ⟨_, by simp [makeHandleFuel, hx, hh, ha, hr, raises, hy, hbody]; rfl⟩
    | ifThenElse cond yes no =>
      have bc : expBudget cond < fuel := by simp_all [expBudget]; omega
      have by' : expBudget yes < fuel := by simp_all [expBudget]; omega
      have bn : expBudget no < fuel := by simp_all [expBudget]; omega
      have byh : expBudget yes + expBudget handler + 1 < fuel := by simp_all [expBudget]; omega
      have bnh : expBudget no + expBudget handler + 1 < fuel := by simp_all [expBudget]; omega
      obtain ⟨cond', hc'⟩ := simplifyFuel_succeeds fuel cond bc
      obtain ⟨yes', hy'⟩ := simplifyFuel_succeeds fuel yes by'
      obtain ⟨no', hn'⟩ := simplifyFuel_succeeds fuel no bn
      obtain ⟨yes'', hy''⟩ := makeHandleFuel_succeeds fuel yes handler depth byh
      obtain ⟨no'', hn''⟩ := makeHandleFuel_succeeds fuel no handler depth bnh
      cases hc : canRaise cond <;> cases hy : canRaise yes <;> cases hn : canRaise no <;>
        exact ⟨_, by simp [makeHandleFuel, hx, hh, ha, canRaiseBounded_eq, hc, hy, hn, hc', hy', hn', hy'', hn'']; rfl⟩
    | _ => exact ⟨_, by simp [makeHandleFuel, hx, hh, ha]; rfl⟩
termination_by fuel
end

end Flapjack.Compiler.Backend.BvlHandle
