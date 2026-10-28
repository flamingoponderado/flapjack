import Flapjack.Compiler.Backend.FlatPattern.Proofs.LookupRelation
import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateExact

/-! Evaluation of generated pattern-binding lets. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.Compiler.Backend
open Flapjack.Basis.Pure.MlString

/-- Index-independent predicates agree on indexed and ordinary maps. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "EVERY_MAPi_simple"]
theorem everyMapIdxSimple {A B : Type} (predicate : B → Prop) (f : Nat → A → B)
    (xs : List A) (independent : ∀ i j x, predicate (f i x) ↔ predicate (f j x)) :
    (∀ y ∈ xs.mapIdx f, predicate y) ↔ ∀ y ∈ xs.map (f 0), predicate y := by
  constructor
  · intro indexed y member
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp member
    obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hx
    have mapped : f i x ∈ xs.mapIdx f := by
      rw [List.mem_mapIdx]
      exact ⟨i, hi, by simp [heq]⟩
    exact (independent i 0 x).mp (indexed _ mapped)
  · intro plain y member
    rw [List.mem_mapIdx] at member
    obtain ⟨i, hi, rfl⟩ := member
    exact (independent i 0 _).mpr (plain _ (List.mem_map.mpr ⟨_, List.getElem_mem hi, rfl⟩))

/-- A helper for the binding-fold simulation. The original HOL theorem has an
additional unused universally quantified variable of an independent type.
Its image premise follows because HOL types are inhabited; this Lean helper
states that premise directly and is therefore not tagged as the HOL theorem. -/
theorem evaluateBindingFold {A C F : Type} (f : A → Option MlString)
    (g : A → FlatLang.Exp) (h : A → FlatSem.Value) (xs : List A)
    (newNames : MlString → Prop) (env : FlatSem.Environment FlatSem.Value)
    (state : FlatSem.State C F) (trace : BackendCommon.Tra) (body : FlatLang.Exp)
    (someName : ∀ x ∈ xs, (f x).isSome = true)
    (fresh : ∀ x ∈ xs, newNames ((f x).getD (ofString "")))
    (evaluateValue : ∀ x ∈ xs, ∀ env2,
      aLookupRel (fun name => ¬ newNames name) Eq env2.v env.v →
      FlatSem.evaluate env2 state [g x] = (state, .val [h x])) :
    ∀ env2, aLookupRel (fun name => ¬ newNames name) Eq env2.v env.v →
      FlatSem.evaluate env2 state [xs.foldr (fun x exp => .let_ trace (f x) (g x) exp) body] =
      FlatSem.evaluate { env2 with v := (xs.reverse.map (fun x => ((f x).getD (ofString ""), h x))) ++ env2.v } state [body] := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    intro env2 related
    have sx := someName x (by simp)
    cases fx : f x with
    | none => simp [fx] at sx
    | some name =>
      have freshName : newNames name := by simpa [fx] using fresh x (by simp)
      have nextRelated : aLookupRel (fun n => ¬ newNames n) Eq ((name, h x) :: env2.v) env.v :=
        ((aLookupRel_cons_false (fun n => ¬ newNames n) Eq name (h x) env2.v env.v).1
          (by simpa using freshName)).2 related
      have evaluated := evaluateValue x (by simp) env2 related
      have rest := ih (fun y hy => someName y (by simp [hy]))
        (fun y hy => fresh y (by simp [hy]))
        (fun y hy => evaluateValue y (by simp [hy]))
        { env2 with v := (name, h x) :: env2.v } nextRelated
      simpa [List.foldr, fx, FlatSem.evaluate, evaluated, FlatSem.fixClock,
        List.reverse_cons, List.map_append, List.append_assoc] using rest

/-- The HOL-shaped version keeps the unused variable's type independent and
inhabited, as HOL types are. It remains untagged until the evaluator and the
translation of HOL's inhabited type variables have been reviewed. The default
for `THE NONE` is unobservable under `someName`. -/
theorem evaluateBindingFoldHOLShape {A B C F : Type} [Nonempty B]
    (f : A → Option MlString) (g : A → FlatLang.Exp) (h : A → FlatSem.Value)
    (xs : List A) (newNames : MlString → Prop) (env : FlatSem.Environment FlatSem.Value)
    (state : FlatSem.State C F) (trace : BackendCommon.Tra) (body : FlatLang.Exp)
    (someName : ∀ x ∈ xs, (f x).isSome = true)
    (fresh : ∀ _ : B, ∀ name, (∃ x, x ∈ xs ∧ (f x).getD (ofString "") = name) → newNames name)
    (evaluateValue : ∀ x ∈ xs, ∀ env2,
      aLookupRel (fun name => ¬ newNames name) Eq env2.v env.v →
      FlatSem.evaluate env2 state [g x] = (state, .val [h x])) :
    ∀ env2, aLookupRel (fun name => ¬ newNames name) Eq env2.v env.v →
      FlatSem.evaluate env2 state [xs.foldr (fun x exp => .let_ trace (f x) (g x) exp) body] =
      FlatSem.evaluate { env2 with v := (xs.reverse.map (fun x => ((f x).getD (ofString ""), h x))) ++ env2.v } state [body] := by
  apply evaluateBindingFold f g h xs newNames env state trace body someName
  · intro x member
    obtain ⟨witness⟩ := ‹Nonempty B›
    exact fresh witness _ ⟨x, member, rfl⟩
  · exact evaluateValue

end Flapjack.Compiler.Backend.FlatPattern
