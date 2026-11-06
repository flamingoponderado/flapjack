import Flapjack.Compiler.Backend.FlatPattern.Proofs.LookupRelation
import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateExact
import Flapjack.Misc.Option
import Mathlib.Data.Set.Basic

/-! Evaluation of generated pattern-binding lets. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.Compiler.Backend
open Flapjack.Basis.Pure.MlString
local instance : Nonempty MlString := ⟨ofString ""⟩

/-- Replacing the sole environment field yields the source environment, even
when the original environment has a different value type. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "env_set_v_noop"]
theorem envSetVNoop {A B : Type} (base : FlatSem.Environment B) (env : FlatSem.Environment A) :
    ({ base with v := env.v } : FlatSem.Environment A) = env := by
  cases base
  cases env
  rfl

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

/-- The original theorem quantifies an unused variable of an independent,
inhabited type over its image premise; that vacuous binder is omitted. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "pat_bindings_evaluate_FOLDR_lemma" 358]
theorem evaluateBindingFold {A C F : Type} (f : A → Option MlString)
    (g : A → FlatLang.Exp) (h : A → FlatSem.Value) (xs : List A)
    (newNames : MlString → Prop) (env : FlatSem.Environment FlatSem.Value)
    (state : FlatSem.State C F) (trace : BackendCommon.Tra) (body : FlatLang.Exp)
    (someName : ∀ x ∈ xs, (f x).isSome = true)
    (fresh : Set.image (Flapjack.holThe ∘ f) {x | x ∈ xs} ⊆ newNames)
    (evaluateValue : ∀ x ∈ xs, ∀ env2,
      aLookupRel (fun name => ¬ newNames name) Eq env2.v env.v →
      FlatSem.evaluate env2 state [g x] = (state, .val [h x])) :
    ∀ env2, aLookupRel (fun name => ¬ newNames name) Eq env2.v env.v →
      FlatSem.evaluate env2 state [xs.foldr (fun x exp => .let_ trace (f x) (g x) exp) body] =
      FlatSem.evaluate { env2 with v := (xs.reverse.map (fun x => (Flapjack.holThe (f x), h x))) ++ env2.v } state [body] := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    intro env2 related
    have sx := someName x (by simp)
    cases fx : f x with
    | none => simp [fx] at sx
    | some name =>
      have freshName : newNames name := by
        apply fresh
        exact ⟨x, by simp, by simp [fx, Flapjack.holThe]⟩
      have nextRelated : aLookupRel (fun n => ¬ newNames n) Eq ((name, h x) :: env2.v) env.v :=
        ((aLookupRel_cons_false (fun n => ¬ newNames n) Eq name (h x) env2.v env.v).1
          (by simpa using freshName)).2 related
      have evaluated := evaluateValue x (by simp) env2 related
      have rest := ih (fun y hy => someName y (by simp [hy]))
        (by
          intro name member
          obtain ⟨y, hy, eq⟩ := member
          exact fresh ⟨y, List.mem_cons_of_mem _ hy, eq⟩)
        (fun y hy => evaluateValue y (by simp [hy]))
        { env2 with v := (name, h x) :: env2.v } nextRelated
      simpa [List.foldr, fx, Flapjack.holThe, FlatSem.evaluate, evaluated, FlatSem.fixClock,
        List.reverse_cons, List.map_append, List.append_assoc] using rest

end Flapjack.Compiler.Backend.FlatPattern
