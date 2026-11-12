module

public import Flapjack.Compiler.Backend.ClosMti
public import Flapjack.Compiler.Backend.Semantics.ClosProps.FreeVars.Append

@[expose] public section

/-! Free-variable preservation during multi-argument collection. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack ClosProps

/-- Application collection preserves free-variable membership in both components. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "collect_apps_fv1"]
theorem collectApps_freeVars (m : Nat) (args : List ClosLang.Exp) (e : ClosLang.Exp) (v : Nat) :
    (freeVars v (ClosMti.collectApps m args e).1 ∨ freeVar v (ClosMti.collectApps m args e).2) ↔
      (freeVars v args ∨ freeVar v e) := by
  cases e with
  | app t loc body more =>
    cases loc with
    | some loc => simp [ClosMti.collectApps]
    | none =>
      simp only [ClosMti.collectApps]
      split
      · have ih := collectApps_freeVars m (args ++ more) body v
        simpa [freeVars_append, freeVar, freeVars, freeVarExp, or_assoc, or_left_comm, or_comm] using ih
      · simp
  | _ => simp [ClosMti.collectApps]
termination_by sizeOf e

/-- Argument collection preserves free variables under the adjusted binder count. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "collect_args_fv1"]
theorem collectArgs_freeVar (m n : Nat) (e : ClosLang.Exp) (n' : Nat) (e' : ClosLang.Exp) (v : Nat)
    (run : ClosMti.collectArgs m n e = (n', e')) :
    freeVar (n' + v) e' ↔ freeVar (n + v) e := by
  cases e with
  | fn name loc vars arity body =>
    cases loc with
    | some loc => simp [ClosMti.collectArgs] at run; obtain ⟨rfl, rfl⟩ := run; rfl
    | none =>
      cases vars with
      | some vars => simp [ClosMti.collectArgs] at run; obtain ⟨rfl, rfl⟩ := run; rfl
      | none =>
        simp only [ClosMti.collectArgs] at run
        split at run
        · have ih := collectArgs_freeVar m (n + arity) body n' e' v run
          simpa [freeVar, freeVars, freeVarExp, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih
        · simp only [Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          rfl
  | _ =>
    simp only [ClosMti.collectArgs, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    rfl
termination_by sizeOf e
end Flapjack.Compiler.Backend.ClosToBvl
