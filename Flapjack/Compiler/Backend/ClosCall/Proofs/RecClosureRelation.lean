module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.RecClosure
public import Flapjack.Compiler.Backend.ClosCall.Proofs.CodeIncludes
public import Flapjack.Compiler.Backend.ClosCall.Compile
public import Flapjack.FiniteMap.SubmapExact

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Recursive-closure relation for direct-call conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosProps

private def toBroad {K V : Type} (code : HolFiniteMapExact K V) : K → Option V := code.lookup
private def ofBroad {K V : Type} (lookup : K → Option V)
    (support : ∃ keys : List K, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact K V :=
  ⟨lookup, support⟩

/-- Canonical finite-map codec for the recursive-closure code parameter. -/
theorem holFmapAsFiniteSupportParamWitness_recClosureRel_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code := by
  cases code
  exact ⟨rfl, rfl, rfl⟩

/-- The direct-call pass relates original recursive groups to their generated
functions and records the required compiler state and installed code. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "recclosure_rel_def"
  (fmap_as_finite_support_parameters := [code])]
noncomputable def recClosureRel (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat)
    (fns1 fns2 : List (Nat × ClosLang.Exp)) : Prop := by
  classical
  exact ∃ g0 : State,
    recClosureWellFormed loc fns1 ∧ wellFormed g0 ∧
    (∀ label, ¬ (label ∈ Set.image Nat.succ {n | n ∈ codeLocations (fns1.map Prod.snd)} ∧
      label ∈ g0.2.map Prod.fst)) ∧
    (∀ label, ¬ (label ∈ (List.range fns1.length).map (fun i => 2 * i + loc + 1) ∧
      label ∈ g0.2.map Prod.fst)) ∧
    let (es, next) := calls (fns1.map Prod.snd) (insertEachSource loc fns1.length g0)
    if List.Forall₂ (fun fn body => ∀ v, DbVars.hasVar v (free [body]).2 = true → v < fn.1)
        fns1 es then
      (∃ tra n, fns2 = callsListSource tra n loc fns1) ∧
      stateExtends (codeListSource loc ((fns1.map Prod.fst).zip es) next) g ∧
      ({n | n ∈ codeLocations (fns1.map Prod.snd)} \ sptDomain next.1) ⊆ allowed ∧
      codeIncludes (codeListSource loc ((fns1.map Prod.fst).zip es) next).2 code
    else
      let (es, next) := calls (fns1.map Prod.snd) g0
      fns2 = (fns1.map Prod.fst).zip es ∧ stateExtends next g ∧
      ({n | n ∈ codeLocations (fns1.map Prod.snd)} \ sptDomain next.1) ⊆ allowed ∧
      {n | n ∈ (List.range fns1.length).map (fun i => 2 * i + loc)} ⊆ allowed ∧
      codeIncludes next.2 code

private theorem stubArities {A : Type} (tr : BackendCommon.Tra) (n loc : Nat)
    (fns : List (Nat × A)) : (callsListSource tr n loc fns).map Prod.fst = fns.map Prod.fst := by
  induction fns generalizing n loc with
  | nil => rfl
  | cons fn rest ih =>
    cases fn
    simp [callsListSource, ih]

/-- The HOL closure-application proof derives this arity preservation when
unfolding `recclosure_rel`: both generated stubs and converted bodies keep
the original function group's arities. -/
theorem recClosureRel_arities (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat)
    (fns1 fns2 : List (Nat × ClosLang.Exp))
    (h : recClosureRel g allowed code loc fns1 fns2) :
    fns2.map Prod.fst = fns1.map Prod.fst := by
  classical
  unfold recClosureRel at h
  obtain ⟨g0, _, _, _, _, h⟩ := h
  dsimp only at h
  split at h
  · obtain ⟨⟨tra, n, rfl⟩, _⟩ := h
    exact stubArities tra n loc fns1
  · cases run : calls (fns1.map Prod.snd) g0 with
    | mk es next =>
      change callsSingList (fns1.map Prod.snd) g0 = (es, next) at run
      rw [run] at h
      obtain ⟨rfl, _⟩ := h
      have len := calls_length (fns1.map Prod.snd) g0 es next run
      simp only [List.length_map] at len
      simp [List.map_fst_zip, len]

/-- Monotonicity used to prove the HOL value well-formedness extension theorem. -/
theorem recClosureRel_mono (g g' : State) (allowed allowed' : Nat → Prop)
    (code code' : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat)
    (fns1 fns2 : List (Nat × ClosLang.Exp))
    (related : recClosureRel g allowed code loc fns1 fns2)
    (codeSub : code.submap code') (stateSub : stateExtends g g')
    (allowedSub : ∀ x, allowed x → allowed' x) : recClosureRel g' allowed' code' loc fns1 fns2 := by
  classical
  unfold recClosureRel at related ⊢
  obtain ⟨g0, wf, stateWf, disjoint, fresh, branch⟩ := related
  refine ⟨g0, wf, stateWf, disjoint, fresh, ?_⟩
  dsimp only at branch ⊢
  split at branch
  next condition =>
    simp only [condition, ↓reduceIte]
    obtain ⟨out, ext, subset, includes⟩ := branch
    refine ⟨out, stateExtends_trans _ _ _ ext stateSub, ?_, ?_⟩
    · exact fun x member => allowedSub x (subset member)
    · exact codeIncludes_submap _ code code' ⟨includes, codeSub⟩
  next condition =>
    simp only [condition, ↓reduceIte]
    obtain ⟨out, ext, subset, group, includes⟩ := branch
    refine ⟨out, stateExtends_trans _ _ _ ext stateSub, ?_, ?_, ?_⟩
    · exact fun x member => allowedSub x (subset member)
    · exact fun x member => allowedSub x (group member)
    · exact codeIncludes_submap _ code code' ⟨includes, codeSub⟩

/-- The state reached by a recursive-closure relation has distinct labels,
so it extends itself. Used in the HOL code-submap preservation proof. -/
theorem recClosureRel_stateExtendsSelf (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat)
    (fns1 fns2 : List (Nat × ClosLang.Exp))
    (related : recClosureRel g allowed code loc fns1 fns2) : stateExtends g g := by
  classical
  unfold recClosureRel at related
  obtain ⟨g0, _, _, _, _, branch⟩ := related
  dsimp only at branch
  split at branch <;> exact stateExtends_refl g branch.2.1.2.2

end Flapjack.Compiler.Backend.ClosCall
