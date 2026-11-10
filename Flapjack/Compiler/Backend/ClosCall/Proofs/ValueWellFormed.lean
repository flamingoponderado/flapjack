module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.RecClosureRelation
public import Flapjack.Compiler.Backend.Semantics.ClosSem

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Direct-call well-formedness for closure values. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem

private def toBroad {K V : Type} (code : HolFiniteMapExact K V) : K → Option V := code.lookup
private def ofBroad {K V : Type} (lookup : K → Option V)
    (support : ∃ keys : List K, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact K V :=
  ⟨lookup, support⟩

/-- Canonical finite-map codec for the value well-formedness code parameter. -/
theorem holFmapAsFiniteSupportParamWitness_valueWellFormed_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code := by
  cases code
  exact ⟨rfl, rfl, rfl⟩

/-- Direct-call well-formedness requires located closures, recursively
well-formed captured values, and a corresponding transformed function group. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "wfv_def"
  (fmap_as_finite_support_parameters := [code])]
def valueWellFormed (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) : Value → Prop
  | .closure none _ _ _ _ | .recclosure none _ _ _ _ => False
  | .closure (some loc) vs env n body =>
      (∀ v ∈ vs, valueWellFormed g allowed code v) ∧
      (∀ v ∈ env, valueWellFormed g allowed code v) ∧
      ∃ fns2, recClosureRel g allowed code loc [(n, body)] fns2
  | .recclosure (some loc) vs env fns _ =>
      (∀ v ∈ vs, valueWellFormed g allowed code v) ∧
      (∀ v ∈ env, valueWellFormed g allowed code v) ∧
      ∃ fns2, recClosureRel g allowed code loc fns fns2
  | .block _ vs => ∀ v ∈ vs, valueWellFormed g allowed code v
  | _ => True
termination_by value => sizeOf value
decreasing_by
  all_goals have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
  all_goals simp_wf
  all_goals omega

end Flapjack.Compiler.Backend.ClosCall
