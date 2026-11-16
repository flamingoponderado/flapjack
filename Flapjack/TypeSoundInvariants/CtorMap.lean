module

public import Flapjack.TypeSoundInvariants
public import Flapjack.TypeSystemHOL.Declarations
public import Flapjack.FiniteMap.BroadCodec

@[expose] public section

/-! Constructor and store typing prerequisites for source type soundness. -/
namespace Flapjack.TypeSoundInvariants
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.TypeSystemHOL
  Flapjack.SemanticPrimitivesHOL

/-- Canonical finite-map parameter codec for constructor typing. -/
theorem holFmapAsFiniteSupportParamWitness_typeCtor_ctMap
    {K A B C : Type} (ctMap : HolFiniteMapExact K (A × List B × C)) (key : K) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad ctMap)).lookup key = ctMap.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad ctMap)).finiteSupport = ctMap.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad ctMap) = ctMap := by
  cases ctMap
  exact ⟨rfl, rfl, rfl⟩

/-- Check a constructor's type entry and its runtime arity. -/
@[hol "cakeml/semantics/proofs/typeSoundInvariantsScript.sml" "type_ctor_def"
  (fmap_as_finite_support_parameters := [ctMap])]
def typeCtor {K A B C Name : Type} (ctMap : HolFiniteMapExact K (A × List B × C))
    (_name : Name) (runtime : Nat × K) (typing : A × List B × C) : Prop :=
  ctMap.lookup runtime.2 = some typing ∧ typing.2.1.length = runtime.1

/-- Canonical finite-map parameter codec for constructor-map well-formedness. -/
theorem holFmapAsFiniteSupportParamWitness_ctMapOk_ctMap
    (ctMap : HolFiniteMapExact Stamp (List MlString × List SemanticT × TypeIdent)) (key : Stamp) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad ctMap)).lookup key = ctMap.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad ctMap)).finiteSupport = ctMap.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad ctMap) = ctMap := by
  cases ctMap
  exact ⟨rfl, rfl, rfl⟩

/-- Well-formedness of the global constructor type map. -/
@[hol "cakeml/semantics/proofs/typeSoundInvariantsScript.sml" "ctMap_ok_def"
  (fmap_as_finite_support_parameters := [ctMap])]
def ctMapOk (ctMap : HolFiniteMapExact Stamp (List MlString × List SemanticT × TypeIdent)) : Prop :=
  (∀ stamp tvs ts ti, ctMap.lookup stamp = some (tvs, ts, ti) →
    ∀ t ∈ ts, checkFreevars 0 tvs t = true) ∧
  (∀ ex tvs ts ti, ctMap.lookup (.exnStamp ex) = some (tvs, ts, ti) →
    tvs = [] ∧ ti = TexnNum) ∧
  (∀ cn id tvs ts ti, ctMap.lookup (.typeStamp cn id) = some (tvs, ts, ti) →
    ti ∉ primTypeNums) ∧
  (∀ stamp1 tvs1 ts1 ti stamp2 tvs2 ts2,
    ctMap.lookup stamp1 = some (tvs1, ts1, ti) ∧
    ctMap.lookup stamp2 = some (tvs2, ts2, ti) → sameType stamp1 stamp2 = true)

end Flapjack.TypeSoundInvariants
