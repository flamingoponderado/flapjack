module

public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.StateRelation
public import Flapjack.Compiler.Backend.ClosAnnotate.Original
public import Flapjack.FiniteMap.CardinalityExact

@[expose] public section

/-! Source-shaped closure-annotation state relation and its connection to the
lookup-oriented simulation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.BackendProps

namespace StateRelationPort
/-- The closure state uses canonical finite-support maps. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end StateRelationPort

/-- The source relation's explicit map-domain and lookup clauses. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "state_rel_def"
  (nested_list_rel_as_mutual := [FunctionsRel]) (fmap_as_finite_support := [refs, code])]
def StateRelSource {C F : Type} (source target : State C F) : Prop :=
  source.clock = target.clock ∧ source.ffi = target.ffi ∧ source.maxApp = target.maxApp ∧
  target.compileOracle = Prod.map id (Prod.map (annotateSource 0) compileSource) ∘ source.compileOracle ∧
  source.compile = (fun config (expressions, auxiliary) =>
    target.compile config (annotateSource 0 expressions, compileSource auxiliary)) ∧
  List.Forall₂ (optionRel ValueRel) source.globals target.globals ∧
  source.refs.domain = target.refs.domain ∧
  (∀ key value, source.refs.lookup key = some value →
    ∃ nextValue, target.refs.lookup key = some nextValue ∧ ClosProps.refRel ValueRel value nextValue) ∧
  source.code.domain = target.code.domain ∧
  (∀ key arity body, source.code.lookup key = some (arity, body) →
    ∃ nextBody, shiftSource (altFreeSource [body]).1 0 arity .ln = [nextBody] ∧
      target.code.lookup key = some (arity, nextBody))

/-- Related annotation states have the same clock. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "state_rel_clocks_eqs"
  (nested_list_rel_as_mutual := [FunctionsRel]) (fmap_as_finite_support := [refs, code])]
theorem stateRelSource_clocks {C F : Type} (source target : State C F)
    (related : StateRelSource source target) : source.clock = target.clock :=
  related.1

/-- Related annotation states have the same maximum application arity. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "state_rel_max_app"
  (nested_list_rel_as_mutual := [FunctionsRel]) (fmap_as_finite_support := [refs, code])]
theorem stateRelSource_maxApp {C F : Type} (source target : State C F)
    (related : StateRelSource source target) : source.maxApp = target.maxApp :=
  related.2.2.1

/-- Pointwise option relations are exactly domain equality plus related
successful lookups. This helper connects the live proof to HOL's map clauses. -/
private theorem lookupRelation_iff {K A B : Type} (left : HolFiniteMapExact K A)
    (right : HolFiniteMapExact K B) (rel : A → B → Prop) :
    (∀ key, optionRel rel (left.lookup key) (right.lookup key)) ↔
      left.domain = right.domain ∧
        ∀ key value, left.lookup key = some value →
          ∃ nextValue, right.lookup key = some nextValue ∧ rel value nextValue := by
  constructor
  · intro h
    constructor
    · ext key
      have related := h key
      cases l : left.lookup key <;> cases r : right.lookup key <;>
        simp_all [HolFiniteMapExact.domain, optionRel]
    · intro key value lookup
      have related := h key
      rw [lookup] at related
      cases r : right.lookup key with
      | none => simp [r, optionRel] at related
      | some nextValue => exact ⟨nextValue, rfl, by simpa [r, optionRel] using related⟩
  · rintro ⟨domains, h⟩ key
    have domainKey := Set.ext_iff.mp domains key
    change (left.lookup key ≠ none) ↔ (right.lookup key ≠ none) at domainKey
    cases l : left.lookup key with
    | none =>
      cases r : right.lookup key <;> simp_all [optionRel]
    | some value =>
      obtain ⟨nextValue, r, related⟩ := h key value l
      simp [r, optionRel, related]

/-- The live code-entry relation expresses the source singleton shift clause. -/
private theorem codeRel_iff_source (arity nextArity : Nat) (body nextBody : ClosLang.Exp) :
    CodeRel (arity, body) (nextArity, nextBody) ↔
      nextArity = arity ∧ shiftSource (altFreeSource [body]).1 0 arity .ln = [nextBody] := by
  simp [CodeRel, annotateSing, altFreeSource_eq_altFree, altFree_singleton,
    shiftSource_eq_shiftList, shiftList, eq_comm]

/-- Pointwise code lookup agrees with the source domain and singleton-shift clauses. -/
private theorem codeLookup_iff (left right : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) :
    (∀ key, optionRel CodeRel (left.lookup key) (right.lookup key)) ↔
      left.domain = right.domain ∧
      ∀ key arity body, left.lookup key = some (arity, body) →
        ∃ nextBody, shiftSource (altFreeSource [body]).1 0 arity .ln = [nextBody] ∧
          right.lookup key = some (arity, nextBody) := by
  rw [lookupRelation_iff]
  constructor
  · rintro ⟨domains, lookup⟩
    refine ⟨domains, ?_⟩
    intro key arity body found
    obtain ⟨⟨nextArity, nextBody⟩, nextFound, related⟩ := lookup key (arity, body) found
    obtain ⟨equal, shifted⟩ := (codeRel_iff_source arity nextArity body nextBody).mp related
    subst nextArity
    exact ⟨nextBody, shifted, nextFound⟩
  · rintro ⟨domains, lookup⟩
    refine ⟨domains, ?_⟩
    intro key entry found
    obtain ⟨arity, body⟩ := entry
    obtain ⟨nextBody, shifted, nextFound⟩ := lookup key arity body found
    exact ⟨(arity, nextBody), nextFound, (codeRel_iff_source arity arity body nextBody).mpr ⟨rfl, shifted⟩⟩

/-- The source-shaped relation and the live simulation relation are equivalent.
This is Flapjack proof infrastructure connecting their two map presentations. -/
theorem stateRelSource_iff {C F : Type} (source target : State C F) :
    StateRelSource source target ↔ StateRel source target := by
  have oracleMap : (pureCo compileInc : C × Program → C × Program) =
      Prod.map id (Prod.map (annotateSource 0) compileSource) := by
    funext p
    obtain ⟨config, expressions, auxiliary⟩ := p
    simp [pureCo, ← compileIncSource_eq_compileInc, compileIncSource]
  have compilerMap : pureCc compileInc target.compile =
      (fun config (expressions, auxiliary) =>
        target.compile config (annotateSource 0 expressions, compileSource auxiliary)) := by
    funext config program
    obtain ⟨expressions, auxiliary⟩ := program
    simp [pureCc, ← compileIncSource_eq_compileInc, compileIncSource]
  simp only [StateRel, StateRelSource, oracleMap, compilerMap]
  rw [codeLookup_iff, lookupRelation_iff]
  simp only [and_assoc]

end Flapjack.Compiler.Backend.ClosAnnotate
