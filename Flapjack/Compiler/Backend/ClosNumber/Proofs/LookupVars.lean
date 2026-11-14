module

public import Flapjack.Compiler.Backend.ClosNumber.Proofs.EvaluateCases

@[expose] public section

/-! Environment lookup under the closure-numbering value relation. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open Flapjack.Compiler.Backend.ClosSem

private theorem lookupVars_none_of_length (indices : List Nat) (env nextEnv : List Value)
    (lengths : env.length = nextEnv.length) :
    lookupVars indices env = none ↔ lookupVars indices nextEnv = none := by
  induction indices with
  | nil => simp [lookupVars]
  | cons index rest ih =>
    have sameAbsent : env[index]? = none ↔ nextEnv[index]? = none := by
      simp only [List.getElem?_eq_none_iff, lengths]
    cases left : env[index]? <;> cases right : nextEnv[index]? <;>
      cases tail : lookupVars rest env <;> cases nextTail : lookupVars rest nextEnv <;>
      simp_all [lookupVars]

/-- Related environments have the same lookup failure behavior. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "lookup_vars_NONE_related_env"]
theorem lookupVars_none_relatedEnv (maxApp : Nat) (indices : List Nat) (env nextEnv : List Value)
    (related : List.Forall₂ (ValueRel maxApp) env nextEnv) :
    lookupVars indices env = none ↔ lookupVars indices nextEnv = none :=
  lookupVars_none_of_length indices env nextEnv related.length_eq

/-- Successful lookups in related environments return related values. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "lookup_vars_SOME_related_env"]
theorem lookupVars_some_relatedEnv (maxApp : Nat) (indices : List Nat)
    (env nextEnv values nextValues : List Value)
    (h : List.Forall₂ (ValueRel maxApp) env nextEnv ∧
      lookupVars indices env = some values ∧ lookupVars indices nextEnv = some nextValues) :
    List.Forall₂ (ValueRel maxApp) values nextValues := by
  obtain ⟨foundValues, found, related⟩ := related_lookupVars maxApp indices env nextEnv values h.1 h.2.1
  rw [h.2.2] at found
  cases found
  exact related

end Flapjack.Compiler.Backend.ClosNumber
