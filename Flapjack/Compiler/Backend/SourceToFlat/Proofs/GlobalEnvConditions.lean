import Flapjack.Compiler.Backend.SourceToFlat.Proofs.GlobalEnv
import Flapjack.Compiler.Backend.BackendCommon.ConstructorTags
import Flapjack.SemanticPrimitivesHOL.Conversions

/-! Constructor-map assumptions used by the original source-to-flat proof. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.Basis.Pure.MlString Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendCommon

private def GlobalMap.toBroadlookup {α β : Type} (m : HolFiniteMapExact α β) := m.lookup
private def GlobalMap.ofBroad {α β : Type} (f : α → Option β)
    (support : ∃ keys : List α, ∀ key, f key ≠ none → key ∈ keys) :
    HolFiniteMapExact α β := ⟨f, support⟩

/-- The constructor map contains the original Boolean stamps. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "has_bools_def"
  (fmap_as_finite_support_parameters := [genv])]
def hasBools (genv : HolFiniteMapExact ConstructorKey Stamp) : Prop :=
  genv.lookup ((trueTag, some FlatLang.boolId), 0) = some (.typeStamp (ofString "True") boolTypeNum) ∧
  genv.lookup ((falseTag, some FlatLang.boolId), 0) = some (.typeStamp (ofString "False") boolTypeNum)

/-- Flapjack finite-map codec witness; it has no separate HOL declaration. -/
theorem holFmapAsFiniteSupportParamWitness_hasBools_genv (genv : HolFiniteMapExact ConstructorKey Stamp) :
    GlobalMap.ofBroad (GlobalMap.toBroadlookup genv) genv.finiteSupport = genv := by cases genv; rfl

/-- The constructor map contains the original list stamps. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "has_lists_def"
  (fmap_as_finite_support_parameters := [genv])]
def hasLists (genv : HolFiniteMapExact ConstructorKey Stamp) : Prop :=
  genv.lookup ((consTag, some FlatSem.listId), 2) = some (.typeStamp (ofString "::") listTypeNum) ∧
  genv.lookup ((nilTag, some FlatSem.listId), 0) = some (.typeStamp (ofString "[]") listTypeNum)

/-- Flapjack finite-map codec witness; it has no separate HOL declaration. -/
theorem holFmapAsFiniteSupportParamWitness_hasLists_genv (genv : HolFiniteMapExact ConstructorKey Stamp) :
    GlobalMap.ofBroad (GlobalMap.toBroadlookup genv) genv.finiteSupport = genv := by cases genv; rfl

/-- The constructor map contains the four original exception stamps. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "has_exns_def"
  (fmap_as_finite_support_parameters := [genv])]
def hasExns {α : Type} (genv : HolFiniteMapExact ((Nat × Option α) × Nat) Stamp) : Prop :=
  genv.lookup ((divTag, none), 0) = some divStamp ∧
  genv.lookup ((chrTag, none), 0) = some chrStamp ∧
  genv.lookup ((subscriptTag, none), 0) = some subscriptStamp ∧
  genv.lookup ((bindTag, none), 0) = some bindStamp

/-- Flapjack finite-map codec witness; it has no separate HOL declaration. -/
theorem holFmapAsFiniteSupportParamWitness_hasExns_genv {α : Type}
    (genv : HolFiniteMapExact ((Nat × Option α) × Nat) Stamp) :
    GlobalMap.ofBroad (GlobalMap.toBroadlookup genv) genv.finiteSupport = genv := by cases genv; rfl

/-- Constructor-map compatibility and injectivity conditions. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "genv_c_ok_def"
  (fmap_as_finite_support_parameters := [genvC])]
def genvCOk (genvC : HolFiniteMapExact ConstructorKey Stamp) : Prop :=
  hasBools genvC ∧ hasExns genvC ∧ hasLists genvC ∧
  (∀ cn1 cn2 l1 l2 stamp1 stamp2,
    genvC.lookup (cn1, l1) = some stamp1 → genvC.lookup (cn2, l2) = some stamp2 →
    (SemanticPrimitivesHOL.ctorSameType (some stamp1) (some stamp2) = true ↔
      FlatSem.ctorSameType (some cn1) (some cn2))) ∧
  (∀ cn1 cn2 l1 l2 stamp,
    genvC.lookup (cn1, l1) = some stamp → genvC.lookup (cn2, l2) = some stamp →
    cn1 = cn2 ∧ l1 = l2)

/-- Flapjack finite-map codec witness; it has no separate HOL declaration. -/
theorem holFmapAsFiniteSupportParamWitness_genvCOk_genvC (genvC : HolFiniteMapExact ConstructorKey Stamp) :
    GlobalMap.ofBroad (GlobalMap.toBroadlookup genvC) genvC.finiteSupport = genvC := by cases genvC; rfl

/-- Every typed constructor key occurs in the corresponding type's constructor list. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "genv_c_tys_ok_def"
  (fmap_as_finite_support_parameters := [genvC, genvTys])]
def genvCTysOk {α β γ δ : Type} (genvC : HolFiniteMapExact ((α × Option β) × γ) δ)
    (genvTys : HolFiniteMapExact β (List (α × γ))) : Prop :=
  ∀ cn tyId arity, (genvC.lookup ((cn, some tyId), arity)).isSome →
    ∃ ctors, genvTys.lookup tyId = some ctors ∧ (cn, arity) ∈ ctors

/-- Flapjack finite-map codec witness; it has no separate HOL declaration. -/
theorem holFmapAsFiniteSupportParamWitness_genvCTysOk_genvC {α β γ δ : Type}
    (genvC : HolFiniteMapExact ((α × Option β) × γ) δ) :
    GlobalMap.ofBroad (GlobalMap.toBroadlookup genvC) genvC.finiteSupport = genvC := by cases genvC; rfl

/-- Flapjack finite-map codec witness; it has no separate HOL declaration. -/
theorem holFmapAsFiniteSupportParamWitness_genvCTysOk_genvTys {α β γ : Type}
    (genvTys : HolFiniteMapExact β (List (α × γ))) :
    GlobalMap.ofBroad (GlobalMap.toBroadlookup genvTys) genvTys.finiteSupport = genvTys := by cases genvTys; rfl

end Flapjack.Compiler.Backend.SourceToFlat
