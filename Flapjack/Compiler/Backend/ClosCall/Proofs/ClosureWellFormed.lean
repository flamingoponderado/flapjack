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

/-- Canonical finite-map codec for the full-application code parameter. -/
theorem holFmapAsFiniteSupportParamWitness_destClosure_fullWellFormed_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code :=
  holFmapAsFiniteSupportParamWitness_destClosure_partialWellFormed_code code key

/-- A full closure application preserves well-formedness of all arguments
and remaining values and identifies the source function body. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "dest_closure_full_wfv"
  (fmap_as_finite_support_parameters := [code])]
theorem destClosure_fullWellFormed {A B : Type} [Nonempty A] [Nonempty B]
    (maxApp : Nat) (loco : Option Nat) (v : Value) (env : List Value)
    (e : ClosLang.Exp) (args rest : List Value) (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (h : destClosure maxApp loco v env = some (.fullApp e args rest) ∧
      valueWellFormed g allowed code v ∧ (∀ y ∈ env, valueWellFormed g allowed code y)) :
    ∃ (_ys : A) (_g01 : B) (loc : Nat) (fns1 fns2 : List (Nat × ClosLang.Exp)) (i : Nat),
      (∀ y ∈ args, valueWellFormed g allowed code y) ∧
      (∀ y ∈ rest, valueWellFormed g allowed code y) ∧
      recClosureRel g allowed code loc fns1 fns2 ∧
      (holEl i fns1).2 = e ∧ i < fns1.length := by
  let : Nonempty (Nat × ClosLang.Exp) := ⟨(0, .var .none 0)⟩
  obtain ⟨run, safe, envSafe⟩ := h
  cases v with
  | closure loc supplied captured arity body =>
    cases loc with
    | none => simp [valueWellFormed] at safe
    | some loc =>
      simp only [destClosure] at run
      split at run <;> try contradiction
      split at run <;> simp only [Option.some.injEq, reduceCtorEq, AppKind.fullApp.injEq] at run
      obtain ⟨rfl, rfl, rfl⟩ := run
      simp only [valueWellFormed] at safe
      obtain ⟨suppliedSafe, capturedSafe, fns2, related⟩ := safe
      refine ⟨Classical.choice inferInstance, Classical.choice inferInstance, loc,
        [(arity, body)], fns2, 0, ?_, ?_, related, by simp [holEl, holHd], by simp⟩
      · intro x hx
        change x ∈ (env.reverse.take (arity - supplied.length)).reverse ++ (supplied ++ captured) at hx
        simp only [List.mem_append] at hx
        rcases hx with h | h | h
        · apply envSafe x
          have := List.mem_of_mem_take (List.mem_reverse.mp h)
          exact List.mem_reverse.mp this
        · exact suppliedSafe x h
        · exact capturedSafe x h
      · intro x hx
        apply envSafe x
        have := List.mem_of_mem_drop (List.mem_reverse.mp hx)
        exact List.mem_reverse.mp this
  | recclosure loc supplied captured fns index =>
    cases loc with
    | none => simp [valueWellFormed] at safe
    | some loc =>
      simp only [destClosure] at run
      split at run <;> try contradiction
      rename_i arity body entry
      split at run <;> try contradiction
      split at run <;> simp only [Option.some.injEq, reduceCtorEq, AppKind.fullApp.injEq] at run
      obtain ⟨rfl, rfl, rfl⟩ := run
      simp only [valueWellFormed] at safe
      obtain ⟨suppliedSafe, capturedSafe, fns2, related⟩ := safe
      have selected := List.getElem?_eq_some_iff.mp entry
      obtain ⟨bound, selected⟩ := selected
      refine ⟨Classical.choice inferInstance, Classical.choice inferInstance, loc,
        fns, fns2, index, ?_, ?_, related, ?_, bound⟩
      · intro x hx
        change x ∈ (env.reverse.take (arity - supplied.length)).reverse ++
          (supplied ++ (List.range fns.length).map (fun i => Value.recclosure (some loc) [] captured fns i) ++ captured) at hx
        simp only [List.mem_append, or_assoc] at hx
        rcases hx with h | h | h | h
        · apply envSafe x
          have := List.mem_of_mem_take (List.mem_reverse.mp h)
          exact List.mem_reverse.mp this
        · exact suppliedSafe x h
        · simp only [List.mem_map, List.mem_range] at h
          obtain ⟨i, _, rfl⟩ := h
          simp only [valueWellFormed]
          exact ⟨by simp, capturedSafe, fns2, related⟩
        · exact capturedSafe x h
      · intro x hx
        apply envSafe x
        have := List.mem_of_mem_drop (List.mem_reverse.mp hx)
        exact List.mem_reverse.mp this
      · rw [holEl_eq_getElem index fns bound, selected]
  | _ => simp [destClosure] at run

end Flapjack.Compiler.Backend.ClosCall
