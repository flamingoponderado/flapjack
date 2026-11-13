module

public import Flapjack.Compiler.Backend.ClosMti
public import Flapjack.Compiler.Backend.Semantics.ClosProps.CodeLocations
public import Flapjack.Compiler.Backend.Semantics.ClosProps.FnAnnotations
public import Mathlib.Data.Set.Basic

@[expose] public section

/-! Closure locations collected by multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack ClosLang ClosProps

/-- Collecting nested applications preserves the union of their code locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "set_code_locs_collect_apps"]
theorem collectApps_codeLocations (maxApp : Nat) (es : List ClosLang.Exp) (e : ClosLang.Exp)
    (es' : List ClosLang.Exp) (e' : ClosLang.Exp)
    (run : ClosMti.collectApps maxApp es e = (es', e')) :
    {x | x ∈ codeLocations [e']} ∪ {x | x ∈ codeLocations es'} =
      {x | x ∈ codeLocations [e]} ∪ {x | x ∈ codeLocations es} := by
  cases e with
  | app trace location inner more =>
    cases location with
    | some loc =>
      simp only [ClosMti.collectApps, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      rfl
    | none =>
      simp only [ClosMti.collectApps] at run
      split at run
      · have ih := collectApps_codeLocations maxApp (es ++ more) inner es' e' run
        rw [ih]
        ext x
        simp [codeLocations, codeLocationsExp, codeLocations_append, or_assoc, or_comm]
      · cases run
        rfl
  | _ =>
    simp only [ClosMti.collectApps, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    rfl
termination_by sizeOf e
/-- Collecting applications preserves function-location annotations in both outputs. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "every_Fn_SOME_collect_apps"]
theorem collectApps_everyFnLocationSome (maxApp : Nat) (es : List ClosLang.Exp) (e : ClosLang.Exp)
    (es' : List ClosLang.Exp) (e' : ClosLang.Exp)
    (run : ClosMti.collectApps maxApp es e = (es', e')) :
    (everyFnLocationSome es' ∧ everyFnLocationSome [e'] ↔
      everyFnLocationSome es ∧ everyFnLocationSome [e]) := by
  have append (xs ys : List ClosLang.Exp) : everyFnLocationSome (xs ++ ys) ↔
      everyFnLocationSome xs ∧ everyFnLocationSome ys := by
    rw [everyFnLocationSome_every (xs ++ ys), everyFnLocationSome_every xs,
      everyFnLocationSome_every ys]
    simp only [List.mem_append, or_imp, forall_and]
  cases e with
  | app trace location inner more =>
    cases location with
    | some loc =>
      simp only [ClosMti.collectApps, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      rfl
    | none =>
      simp only [ClosMti.collectApps] at run
      split at run
      · have ih := collectApps_everyFnLocationSome maxApp (es ++ more) inner es' e' run
        simp only [append] at ih
        simpa [everyFnLocationSome, fnLocationSomeExp, and_assoc, and_left_comm, and_comm] using ih
      · cases run
        rfl
  | _ =>
    simp only [ClosMti.collectApps, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    rfl
termination_by sizeOf e


end Flapjack.Compiler.Backend.ClosToBvl
