module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.ValueWellFormed
public import Flapjack.Compiler.Backend.Semantics.ClosSem.Call

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Well-formedness under closure application. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem

private def toBroad {K V : Type} (code : HolFiniteMapExact K V) : K → Option V := code.lookup
private def ofBroad {K V : Type} (lookup : K → Option V)
    (support : ∃ keys : List K, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact K V :=
  ⟨lookup, support⟩

/-- Canonical finite-map codec for the code parameter. -/
theorem holFmapAsFiniteSupportParamWitness_destClosure_partialWellFormed_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code := by
  cases code
  exact ⟨rfl, rfl, rfl⟩

/-- A partial closure application preserves value well-formedness. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "dest_closure_partial_wfv"
  (fmap_as_finite_support_parameters := [code])]
theorem destClosure_partialWellFormed (maxApp : Nat) (loco : Option Nat) (v : Value) (env : List Value)
    (x : Value) (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (h : destClosure maxApp loco v env = some (.partialApp x) ∧
      (∀ y ∈ env, valueWellFormed g allowed code y) ∧ valueWellFormed g allowed code v) :
    valueWellFormed g allowed code x := by
  obtain ⟨run, envSafe, safe⟩ := h
  cases v with
  | closure loc supplied captured arity body =>
    cases loc with
    | none => simp [valueWellFormed] at safe
    | some loc =>
      simp only [destClosure] at run
      split at run <;> try contradiction
      split at run <;> try contradiction
      simp only [Option.some.injEq, AppKind.partialApp.injEq] at run
      subst x
      simp only [valueWellFormed] at safe ⊢
      simp only [List.mem_append, or_imp, forall_and]
      exact ⟨⟨envSafe, safe.1⟩, safe.2⟩
      all_goals simp_all
  | recclosure loc supplied captured fns index =>
    cases loc with
    | none => simp [valueWellFormed] at safe
    | some loc =>
      simp only [destClosure] at run
      split at run <;> try contradiction
      split at run <;> try contradiction
      split at run <;> try contradiction
      simp only [Option.some.injEq, AppKind.partialApp.injEq] at run
      subst x
      simp only [valueWellFormed] at safe ⊢
      simp only [List.mem_append, or_imp, forall_and]
      exact ⟨⟨envSafe, safe.1⟩, safe.2⟩
      all_goals simp_all
  | _ => simp [destClosure] at run
end Flapjack.Compiler.Backend.ClosCall
