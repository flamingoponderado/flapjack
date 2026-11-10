module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.ValueWellFormed
public import Flapjack.Compiler.Backend.ClosCall.Proofs.ValueRelation

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Existence of a direct-call target value for every well-formed source value. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem ClosLang

private def toBroad {K V : Type} (code : HolFiniteMapExact K V) : K → Option V := code.lookup
private def ofBroad {K V : Type} (lookup : K → Option V)
    (support : ∃ keys : List K, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact K V :=
  ⟨lookup, support⟩

/-- Canonical finite-map codec for the code parameter. -/
theorem holFmapAsFiniteSupportParamWitness_valueRel_exists_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code := by
  cases code
  exact ⟨rfl, rfl, rfl⟩

private theorem listExists {A B : Type} (R : A → B → Prop) (xs : List A)
    (h : ∀ x ∈ xs, ∃ y, R x y) : ∃ ys, List.Forall₂ R xs ys := by
  induction xs with
  | nil => exact ⟨[], .nil⟩
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := h x (by simp)
    obtain ⟨ys, hys⟩ := ih (by intro z hz; exact h z (by simp [hz]))
    exact ⟨y :: ys, .cons hy hys⟩

private theorem singletonGroup (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc n : Nat) (body : ClosLang.Exp)
    (fns : List (Nat × ClosLang.Exp)) (h : recClosureRel g allowed code loc [(n, body)] fns) :
    ∃ body', fns = [(n, body')] := by
  have arities := recClosureRel_arities g allowed code loc [(n, body)] fns h
  cases fns with
  | nil => simp at arities
  | cons f fs =>
    obtain ⟨a, e⟩ := f
    cases fs with
    | nil => simp at arities; subst a; exact ⟨e, rfl⟩
    | cons f fs => simp at arities

/-- Every well-formed value has a direct-call-related target value. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "v_rel_exists"
  (fmap_as_finite_support_parameters := [code])]
theorem valueRel_exists (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (v : Value)
    (safe : valueWellFormed g allowed code v) : ∃ v2, valueRel g allowed code v v2 := by
  cases v with
  | number n => exact ⟨.number n, by simp [valueRel]⟩
  | word64 n => exact ⟨.word64 n, by simp [valueRel]⟩
  | byteVector bytes => exact ⟨.byteVector bytes, by simp [valueRel]⟩
  | refPtr b n => exact ⟨.refPtr b n, by simp [valueRel]⟩
  | block tag values =>
    simp only [valueWellFormed] at safe
    obtain ⟨ys, rel⟩ := listExists (valueRel g allowed code) values (by
      intro x hx
      exact valueRel_exists g allowed code x (safe x hx))
    exact ⟨.block tag ys, (valueRel_sourceEquations g allowed code).1 _ _ _ |>.mpr ⟨ys, rfl, rel⟩⟩
  | closure loco values env n body =>
    cases loco with
    | none => simp [valueWellFormed] at safe
    | some loc =>
      simp only [valueWellFormed] at safe
      obtain ⟨vsSafe, envSafe, fns, closure⟩ := safe
      obtain ⟨body', rfl⟩ := singletonGroup g allowed code loc n body fns closure
      obtain ⟨vs', vsRel⟩ := listExists (valueRel g allowed code) values (by
        intro x hx; exact valueRel_exists g allowed code x (vsSafe x hx))
      obtain ⟨env', envRel'⟩ := listExists (valueRel g allowed code) env (by
        intro x hx; exact valueRel_exists g allowed code x (envSafe x hx))
      have envRelated : envRel (valueRel g allowed code) env env' 0 [(n, body')] := by
        unfold envRel
        rw [if_pos envRel'.length_eq]
        exact envRel'
      exact ⟨.closure (some loc) vs' env' n body',
        (valueRel_sourceEquations g allowed code).2.1 _ _ _ _ _ _ |>.mpr
          ⟨loc, vs', env', body', closure, rfl, rfl, vsRel, envRelated⟩⟩
  | recclosure loco values env fns i =>
    cases loco with
    | none => simp [valueWellFormed] at safe
    | some loc =>
      simp only [valueWellFormed] at safe
      obtain ⟨vsSafe, envSafe, fns', closure⟩ := safe
      obtain ⟨vs', vsRel⟩ := listExists (valueRel g allowed code) values (by
        intro x hx; exact valueRel_exists g allowed code x (vsSafe x hx))
      obtain ⟨env', envRel'⟩ := listExists (valueRel g allowed code) env (by
        intro x hx; exact valueRel_exists g allowed code x (envSafe x hx))
      have envRelated : envRel (valueRel g allowed code) env env' fns'.length fns' := by
        unfold envRel
        rw [if_pos envRel'.length_eq]
        exact envRel'
      exact ⟨.recclosure (some loc) vs' env' fns' i,
        (valueRel_sourceEquations g allowed code).2.2 _ _ _ _ _ _ |>.mpr
          ⟨loc, vs', env', fns', closure, rfl, rfl, vsRel, envRelated⟩⟩
termination_by sizeOf v
decreasing_by
  all_goals subst_vars
  all_goals have bound := List.sizeOf_lt_of_mem (show x ∈ _ from ‹x ∈ _›)
  all_goals simp_wf
  all_goals omega
end Flapjack.Compiler.Backend.ClosCall
