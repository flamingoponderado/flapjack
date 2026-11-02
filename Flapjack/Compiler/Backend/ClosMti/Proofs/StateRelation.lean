import Flapjack.Compiler.Backend.ClosMti.Proofs.Relations
import Flapjack.Compiler.Backend.Semantics.ClosSem.State
import Flapjack.Compiler.Backend.BackendProps.Pure

/-! State relation for multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open ClosSem BackendProps

private def maptoBroadlookup {K V : Type} (map : HolFiniteMapExact K V) : K → Option V := map.lookup
private def mapofBroad {K V : Type} (lookup : K → Option V)
    (support : ∃ keys : List K, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact K V :=
  ⟨lookup, support⟩

/-- Canonical lookup and support roundtrip for the first map parameter. -/
theorem holFmapAsFiniteSupportParamWitness_fmapRel_first {K A : Type} (first : HolFiniteMapExact K A) :
    mapofBroad (maptoBroadlookup first) first.finiteSupport = first := by cases first; rfl

/-- Canonical lookup and support roundtrip for the second map parameter. -/
theorem holFmapAsFiniteSupportParamWitness_fmapRel_second {K B : Type} (second : HolFiniteMapExact K B) :
    mapofBroad (maptoBroadlookup second) second.finiteSupport = second := by cases second; rfl

/-- Equal finite-map domains with related values at every source key. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "FMAP_REL_def"
  (fmap_as_finite_support_parameters := [first, second])]
def fmapRel {K A B : Type} (r : A → B → Prop) (first : HolFiniteMapExact K A)
    (second : HolFiniteMapExact K B) : Prop :=
  (∀ k, first.lookup k ≠ none ↔ second.lookup k ≠ none) ∧
    ∀ k v, first.lookup k = some v → ∃ w, second.lookup k = some w ∧ r v w

/-- The closure-state finite-map representation and its lookup view roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Relate closure states across multi-argument introduction. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "state_rel_def"
  (fmap_as_finite_support := [refs, code])]
noncomputable def StateRel {C F : Type} (source target : State C F) : Prop :=
  (∀ n, (source.compileOracle n).2.2 = [] ∧
    ∀ e ∈ (source.compileOracle n).2.1, ClosProps.noMti e) ∧
  source.code = HolFiniteMapExact.empty ∧ target.code = HolFiniteMapExact.empty ∧
  target.maxApp = source.maxApp ∧ 1 ≤ source.maxApp ∧
  target.clock = source.clock ∧ target.ffi = source.ffi ∧
  List.Forall₂ (ValueRelOpt source.maxApp) source.globals target.globals ∧
  fmapRel (RefRel source.maxApp) source.refs target.refs ∧
  source.compile = pureCc (compileInc source.maxApp) target.compile ∧
  target.compileOracle = pureCo (compileInc source.maxApp) ∘ source.compileOracle

/-- Related states agree on clock and application limit. -/
theorem stateRel_clock_maxApp {C F : Type} {source target : State C F}
    (related : StateRel source target) :
    source.clock = target.clock ∧ source.maxApp = target.maxApp ∧ 1 ≤ target.maxApp := by
  obtain ⟨_, _, _, maxEq, maxPos, clockEq, _⟩ := related
  exact ⟨clockEq.symm, maxEq.symm, maxEq ▸ maxPos⟩

end Flapjack.Compiler.Backend.ClosMti
