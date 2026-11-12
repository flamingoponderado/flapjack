module

public import Flapjack.Compiler.Backend.BvlHandle.Compile
public import Flapjack.Compiler.Backend.DbVars.Proofs.Lookup
public import Flapjack.Compiler.Backend.Semantics.BvlSem.State
public import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateHOL

@[expose] public section

/-! Environment agreement on the handler compiler's live variables. -/
namespace Flapjack.Compiler.Backend.BvlHandle.Proofs
open Flapjack.Compiler.Backend.DbVars
open Flapjack.Compiler.Backend.BvlSem

/-- Two lists have the same length and agree at every live index. This is
the bounded-index form of HOL's indexed list relation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "env_rel_def"]
def envRel {α : Type} (live : DbVarSet) (source target : List α) : Prop :=
  source.length = target.length ∧
    ∀ index, index < source.length → hasVar index live = true → source[index]? = target[index]?

/-- The option-lookup presentation agrees with bounded element comparison.
This supports the source `LIST_RELi` comparison and has no separate HOL declaration. -/
theorem envRel_getElem_iff {α : Type} (live : DbVarSet) (source target : List α) :
    envRel live source target ↔ source.length = target.length ∧
      ∀ (i : Nat) (hs : i < source.length) (ht : i < target.length),
        hasVar i live = true → source[i] = target[i] := by
  constructor
  · rintro ⟨length, agree⟩
    refine ⟨length, ?_⟩
    intro i hs ht present
    have equal := agree i hs present
    simpa only [List.getElem?_eq_getElem hs, List.getElem?_eq_getElem ht, Option.some.injEq] using equal
  · rintro ⟨length, agree⟩
    refine ⟨length, ?_⟩
    intro i hs present
    have ht : i < target.length := by omega
    simpa only [List.getElem?_eq_getElem hs, List.getElem?_eq_getElem ht] using
      congrArg some (agree i hs ht present)

/-- Flattening live-variable annotations does not change environment agreement. -/
theorem envRel_flatten {α : Type} (live : DbVarSet) (source target : List α) :
    envRel (varsFlatten live) source target ↔ envRel live source target := by
  simp [envRel, hasVarVarsFlatten]

/-- The live-variable relation returned by an optional cut implies the input relation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "OptionalLetLet_limit"]
theorem optionalLetLet_limit {α : Type} (ys : List Bvl.Exp) (resultLive : DbVarSet)
    (resultSize : Nat) (resultNoRaise : Bool) (body : Bvl.Exp)
    (source target : List α) (live : DbVarSet) (size limit : Nat) (noRaise : Bool)
    (premises : (ys, resultLive, resultSize, resultNoRaise) =
        optionalLetLet body source.length live size limit noRaise ∧
      envRel resultLive source target) : envRel live source target := by
  obtain ⟨compiled, related⟩ := premises
  by_cases small : size < limit
  · simp only [optionalLetLet, small, ↓reduceIte, Prod.mk.injEq] at compiled
    obtain ⟨_, rfl, _, _⟩ := compiled
    exact related
  · simp only [optionalLetLet, small, ↓reduceIte, Prod.mk.injEq] at compiled
    obtain ⟨_, rfl, _, _⟩ := compiled
    exact (envRel_flatten live source target).1 related

/-- Materialized live-variable lookup agrees with direct membership. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "IS_SOME_lookup_db_to_set"]
theorem isSomeLookupDbToSet (n : Nat) (live : DbVarSet) :
    (sptLookup n (dbToSet live)).isSome = hasVar n live := by
  rw [dbToSet, lookupDbToSetAcc]
  cases hasVar n live <;> simp

/-- Related environments have the same length. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "env_rel_length"]
theorem envRel_length {α : Type} (live : DbVarSet) (source target : List α)
    (related : envRel live source target) : target.length = source.length := related.1.symm

/-- Every environment agrees with itself at its live indices. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "env_rel_refl"]
theorem envRel_refl {α : Type} (live : DbVarSet) (env : List α) : envRel live env env := by
  exact ⟨rfl, fun _ _ _ => rfl⟩

/-- Agreement on a union of live variables is agreement on both sets. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "env_rel_mk_Union"]
theorem envRel_mkUnion {α : Type} (left right : DbVarSet) (source target : List α) :
    envRel (mkUnion left right) source target ↔ envRel left source target ∧ envRel right source target := by
  simp only [envRel, hasVar_mkUnion, Bool.or_eq_true]
  constructor
  · intro ⟨length, agree⟩
    exact ⟨⟨length, fun i bound live => agree i bound (Or.inl live)⟩,
      ⟨length, fun i bound live => agree i bound (Or.inr live)⟩⟩
  · intro ⟨⟨length, leftAgree⟩, _, rightAgree⟩
    exact ⟨length, fun i bound live => live.elim (leftAgree i bound) (rightAgree i bound)⟩

/-- Replacing non-live values with zero retains exactly the agreement needed
by the handler compiler's environment relation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "env_rel_MAPi"]
theorem envRel_mask (live : DbVarSet) (env : List Value) :
    envRel live env (env.mapIdx fun index value =>
      if hasVar index live then value else .number 0) := by
  constructor
  · simp
  · intro index _ present
    simp [List.getElem?_mapIdx, present]

/-- Related environments return the same live value even when another
suffix is appended to the target environment. -/
theorem envRel_live_lookup (live : DbVarSet) (source target extra : List Value)
    (related : envRel live source target) (index : Nat)
    (inBounds : index < source.length) (present : hasVar index live = true) :
    (target ++ extra)[index]? = source[index]? := by
  have targetBound : index < target.length := by rw [← related.1]; exact inBounds
  simpa [List.getElem?_append, targetBound] using (related.2 index inBounds present).symm

/-- The handler compiler's variable case preserves non-type-error
evaluation under its live-variable environment relation. -/
theorem evaluate_compileSing_var {C F : Type} (limit index : Nat)
    (source target extra : List Value) (state : State C F)
    (related : envRel (compileSing limit source.length (.var index)).2.1 source target)
    (notType : (evaluate [.var index] source state).1 ≠ .err (.abort .typeError)) :
    evaluate [(compileSing limit source.length (.var index)).1] (target ++ extra) state =
      evaluate [.var index] source state := by
  by_cases inBounds : index < source.length
  · have live : hasVar index (compileSing limit source.length (.var index)).2.1 = true := by
      simp [compileSing, inBounds, hasVar]
    have lookup := envRel_live_lookup _ source target extra related index inBounds live
    simp only [compileSing, inBounds, ↓reduceIte, evaluate]
    rw [lookup]
  · cases found : source[index]? with
    | none => simp [evaluate, found] at notType
    | some value =>
      have bound := List.getElem?_eq_some_iff.mp found |>.1
      exact False.elim (inBounds bound)

/-- The force case uses the same live lookup; the thunk's recursive body
runs in its own argument environment. -/
theorem evaluate_compileSing_force {C F : Type} (limit location index : Nat)
    (source target extra : List Value) (state : State C F)
    (related : envRel (compileSing limit source.length (.force location index)).2.1 source target)
    (notType : (evaluate [.force location index] source state).1 ≠ .err (.abort .typeError)) :
    evaluate [(compileSing limit source.length (.force location index)).1] (target ++ extra) state =
      evaluate [.force location index] source state := by
  by_cases inBounds : index < source.length
  · have live : hasVar index (compileSing limit source.length (.force location index)).2.1 = true := by
      simp [compileSing, inBounds, hasVar]
    have lookup := envRel_live_lookup _ source target extra related index inBounds live
    simp only [compileSing, inBounds, ↓reduceIte, evaluate]
    rw [lookup]
  · cases found : source[index]? with
    | none => simp [evaluate, found] at notType
    | some value =>
      have bound := List.getElem?_eq_some_iff.mp found |>.1
      exact False.elim (inBounds bound)

/-- Extending both environments by identical values preserves agreement
under a corresponding de Bruijn shift. -/
theorem envRel_prepend_shift (live : DbVarSet) (source target before : List Value)
    (related : envRel (.shift before.length live) source target) :
    envRel live (before ++ source) (before ++ target) := by
  obtain ⟨length, agree⟩ := related
  constructor
  · simp [length]
  · intro index bound present
    by_cases inside : index < before.length
    · simp [List.getElem?_append, inside]
    · have sourceBound : index - before.length < source.length := by
        simp only [List.length_append] at bound
        omega
      have indexEq : index - before.length + before.length = index := by omega
      have liveShift : hasVar (index - before.length) (.shift before.length live) = true := by
        simpa [hasVar, indexEq] using present
      have same := agree (index - before.length) sourceBound liveShift
      simpa [List.getElem?_append, inside] using same

end Flapjack.Compiler.Backend.BvlHandle.Proofs
