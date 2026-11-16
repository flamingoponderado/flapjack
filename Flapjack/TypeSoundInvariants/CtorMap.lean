module

public import Flapjack.TypeSoundInvariants
public import Flapjack.TypeSystemHOL.Declarations
public import Flapjack.FiniteMap.BroadCodec
public import Flapjack.SemanticPrimitivesHOL.Conversions

@[expose] public section

/-! Constructor and store typing prerequisites for source type soundness. -/
namespace Flapjack.TypeSoundInvariants
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.TypeSystemHOL
  Flapjack.SemanticPrimitivesHOL

/-- The source's three store-typing entries. -/
@[hol "cakeml/semantics/proofs/typeSoundInvariantsScript.sml" "store_t"]
inductive StoreT where
  | refT : SemanticT → StoreT
  | w8arrayT : StoreT
  | varrayT : SemanticT → StoreT

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

/-- The exception-map parameter's canonical codec. -/
theorem holFmapAsFiniteSupportParamWitness_ctMapHasExns_ctMap {A B : Type}
    (ctMap : HolFiniteMapExact Stamp (List A × List B × Nat)) (key : Stamp) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad ctMap)).lookup key = ctMap.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad ctMap)).finiteSupport = ctMap.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad ctMap) = ctMap := by
  cases ctMap
  exact ⟨rfl, rfl, rfl⟩

/-- The global map contains all primitive exception constructors. -/
@[hol "cakeml/semantics/proofs/typeSoundInvariantsScript.sml" "ctMap_has_exns_def"
  (fmap_as_finite_support_parameters := [ctMap])]
def ctMapHasExns {A B : Type} (ctMap : HolFiniteMapExact Stamp (List A × List B × Nat)) : Prop :=
  ctMap.lookup bindStamp = some ([], [], TexnNum) ∧
  ctMap.lookup chrStamp = some ([], [], TexnNum) ∧
  ctMap.lookup divStamp = some ([], [], TexnNum) ∧
  ctMap.lookup subscriptStamp = some ([], [], TexnNum)

/-- The list-map parameter's canonical codec. -/
theorem holFmapAsFiniteSupportParamWitness_ctMapHasLists_ctMap
    (ctMap : HolFiniteMapExact Stamp (List MlString × List SemanticT × Nat)) (key : Stamp) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad ctMap)).lookup key = ctMap.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad ctMap)).finiteSupport = ctMap.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad ctMap) = ctMap := by
  cases ctMap
  exact ⟨rfl, rfl, rfl⟩

/-- The global map contains exactly the primitive list constructors at their stamp. -/
@[hol "cakeml/semantics/proofs/typeSoundInvariantsScript.sml" "ctMap_has_lists_def"
  (fmap_as_finite_support_parameters := [ctMap])]
def ctMapHasLists (ctMap : HolFiniteMapExact Stamp (List MlString × List SemanticT × Nat)) : Prop :=
  ctMap.lookup (.typeStamp (ofString "[]") listTypeNum) = some ([ofString "'a"], [], TlistNum) ∧
  ctMap.lookup (.typeStamp (ofString "::") listTypeNum) =
    some ([ofString "'a"], [.var (ofString "'a"), Tlist (.var (ofString "'a"))], TlistNum) ∧
  (∀ cn, cn ≠ ofString "::" ∧ cn ≠ ofString "[]" →
    ctMap.lookup (.typeStamp cn listTypeNum) = none)

/-- The boolean-map parameter's canonical codec. -/
theorem holFmapAsFiniteSupportParamWitness_ctMapHasBools_ctMap {A B : Type}
    (ctMap : HolFiniteMapExact Stamp (List A × List B × Nat)) (key : Stamp) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad ctMap)).lookup key = ctMap.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad ctMap)).finiteSupport = ctMap.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad ctMap) = ctMap :=
  holFmapAsFiniteSupportParamWitness_ctMapHasExns_ctMap ctMap key

/-- The global map contains exactly the primitive boolean constructors at their stamp. -/
@[hol "cakeml/semantics/proofs/typeSoundInvariantsScript.sml" "ctMap_has_bools_def"
  (fmap_as_finite_support_parameters := [ctMap])]
def ctMapHasBools {A B : Type} (ctMap : HolFiniteMapExact Stamp (List A × List B × Nat)) : Prop :=
  ctMap.lookup (.typeStamp (ofString "True") boolTypeNum) = some ([], [], TboolNum) ∧
  ctMap.lookup (.typeStamp (ofString "False") boolTypeNum) = some ([], [], TboolNum) ∧
  (∀ cn, cn ≠ ofString "True" ∧ cn ≠ ofString "False" →
    ctMap.lookup (.typeStamp cn boolTypeNum) = none)

/-- The complete constructor-map invariant's canonical codec. -/
theorem holFmapAsFiniteSupportParamWitness_goodCtMap_ctMap
    (ctMap : HolFiniteMapExact Stamp (List MlString × List SemanticT × TypeIdent)) (key : Stamp) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad ctMap)).lookup key = ctMap.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad ctMap)).finiteSupport = ctMap.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad ctMap) = ctMap :=
  holFmapAsFiniteSupportParamWitness_ctMapOk_ctMap ctMap key

/-- The complete constructor-map well-formedness requirement. -/
@[hol "cakeml/semantics/proofs/typeSoundInvariantsScript.sml" "good_ctMap_def"
  (fmap_as_finite_support_parameters := [ctMap])]
def goodCtMap (ctMap : HolFiniteMapExact Stamp (List MlString × List SemanticT × TypeIdent)) : Prop :=
  ctMapOk ctMap ∧ ctMapHasBools ctMap ∧ ctMapHasExns ctMap ∧ ctMapHasLists ctMap

end Flapjack.TypeSoundInvariants
