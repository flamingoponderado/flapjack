import Mathlib.Data.Set.Disjoint
import Flapjack.FiniteMap.UnionExact
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

/-- Compatible fresh constructor entries preserve constructor-map validity. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "genv_c_ok_extend"
  (fmap_as_finite_support_parameters := [c, cExt])]
theorem genvCOk_extend (c : HolFiniteMapExact ConstructorKey Stamp)
    (cExt : HolFiniteMapExact ConstructorKey Stamp)
    (premises : genvCOk c ∧
      (∀ cn arity stamp, cExt.lookup (cn, arity) = some stamp →
        (sameType (.exnStamp 0) stamp = true ↔ cn.2 = none) ∧
        (∀ cn' arity' stamp', cExt.lookup (cn', arity') = some stamp' →
          (sameType stamp stamp' = true ↔ FlatSem.ctorSameType (some cn) (some cn')) ∧
          (stamp = stamp' → cn = cn' ∧ arity = arity')) ∧
        (∀ cn' arity' stamp', c.lookup (cn', arity') = some stamp' →
          stamp ≠ stamp' ∧ (cn.2 ≠ none → cn.2 ≠ cn'.2) ∧
          (∀ s s' n, stamp = .typeStamp s n → stamp' ≠ .typeStamp s' n)))) :
    genvCOk (c.union cExt) := by
  obtain ⟨valid, ext⟩ := premises
  have oldLookup {key value} (h : c.lookup key = some value) :
      (c.union cExt).lookup key = some value := by simp [HolFiniteMapExact.lookup_union, h]
  have classify (cn : FlatLang.CtorId × FlatLang.TypeId) (arity : Nat) (stamp : Stamp)
      (h : (c.union cExt).lookup (cn, arity) = some stamp) :
      c.lookup (cn, arity) = some stamp ∨ cExt.lookup (cn, arity) = some stamp := by
    cases old : c.lookup (cn, arity) with
    | none => right; simpa [HolFiniteMapExact.lookup_union, old] using h
    | some value => left; simpa [HolFiniteMapExact.lookup_union, old] using h
  have oldClass (cn : FlatLang.CtorId × FlatLang.TypeId) (arity : Nat) (stamp : Stamp)
      (h : c.lookup (cn, arity) = some stamp) :
      sameType (.exnStamp 0) stamp = true ↔ cn.2 = none := by
    have compat := valid.2.2.2.1 (divTag, none) cn 0 arity divStamp stamp valid.2.1.1 h
    cases stamp <;> simpa [SemanticPrimitivesHOL.ctorSameType, sameType,
      FlatSem.ctorSameType, divStamp, eq_comm] using compat
  have mixed (newCn oldCn : FlatLang.CtorId × FlatLang.TypeId) (newArity oldArity : Nat)
      (newStamp oldStamp : Stamp) (hNew : cExt.lookup (newCn, newArity) = some newStamp)
      (hOld : c.lookup (oldCn, oldArity) = some oldStamp) :
      (sameType newStamp oldStamp = true ↔ FlatSem.ctorSameType (some newCn) (some oldCn)) := by
    have newClass := (ext newCn newArity newStamp hNew).1
    have oldClass' := oldClass oldCn oldArity oldStamp hOld
    have cross := (ext newCn newArity newStamp hNew).2.2 oldCn oldArity oldStamp hOld
    obtain ⟨_, diffType, diffStamp⟩ := cross
    clear ext valid hNew hOld oldLookup classify oldClass c cExt
    rcases newCn with ⟨newTag, newType⟩
    rcases oldCn with ⟨oldTag, oldType⟩
    cases newStamp <;> cases oldStamp <;> cases newType <;> cases oldType <;>
      simp_all [sameType, FlatSem.ctorSameType]
    exact Ne.symm diffStamp
  refine ⟨⟨oldLookup valid.1.1, oldLookup valid.1.2⟩,
    ⟨oldLookup valid.2.1.1, oldLookup valid.2.1.2.1, oldLookup valid.2.1.2.2.1, oldLookup valid.2.1.2.2.2⟩,
    ⟨oldLookup valid.2.2.1.1, oldLookup valid.2.2.1.2⟩, ?_, ?_⟩
  · intro cn1 cn2 a1 a2 s1 s2 h1 h2
    rcases classify cn1 a1 s1 h1 with old1 | new1 <;>
      rcases classify cn2 a2 s2 h2 with old2 | new2
    · exact valid.2.2.2.1 cn1 cn2 a1 a2 s1 s2 old1 old2
    · have reverse := mixed cn2 cn1 a2 a1 s2 s1 new2 old1
      have stampSym : sameType s1 s2 = sameType s2 s1 := by
        cases s1 <;> cases s2 <;> simp [sameType, eq_comm]
      have keySym : FlatSem.ctorSameType (some cn2) (some cn1) ↔
          FlatSem.ctorSameType (some cn1) (some cn2) := by simp [FlatSem.ctorSameType, eq_comm]
      simpa only [SemanticPrimitivesHOL.ctorSameType, stampSym, keySym] using reverse
    · simpa [SemanticPrimitivesHOL.ctorSameType] using mixed cn1 cn2 a1 a2 s1 s2 new1 old2
    · simpa [SemanticPrimitivesHOL.ctorSameType] using (ext cn1 a1 s1 new1).2.1 cn2 a2 s2 new2 |>.1
  · intro cn1 cn2 a1 a2 stamp h1 h2
    rcases classify cn1 a1 stamp h1 with old1 | new1 <;>
      rcases classify cn2 a2 stamp h2 with old2 | new2
    · exact valid.2.2.2.2 cn1 cn2 a1 a2 stamp old1 old2
    · exact False.elim ((ext cn2 a2 stamp new2).2.2 cn1 a1 stamp old1 |>.1 rfl)
    · exact False.elim ((ext cn1 a1 stamp new1).2.2 cn2 a2 stamp old2 |>.1 rfl)
    · exact (ext cn1 a1 stamp new1).2.1 cn2 a2 stamp new2 |>.2 rfl

/-- Canonical finite-map parameter codec witnesses. -/
theorem holFmapAsFiniteSupportParamWitness_genvCOk_extend_c (c : HolFiniteMapExact ConstructorKey Stamp) :
    GlobalMap.ofBroad (GlobalMap.toBroadlookup c) c.finiteSupport = c := by cases c; rfl

theorem holFmapAsFiniteSupportParamWitness_genvCOk_extend_cExt (cExt : HolFiniteMapExact ConstructorKey Stamp) :
    GlobalMap.ofBroad (GlobalMap.toBroadlookup cExt) cExt.finiteSupport = cExt := by cases cExt; rfl

/-- Disjoint type tables preserve constructor/type consistency under union. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "genv_c_tys_ok_extend"
  (fmap_as_finite_support_parameters := [c, cExt, tys, tysExt])]
theorem genvCTysOk_extend {α β γ δ : Type}
    (c : HolFiniteMapExact ((α × Option β) × γ) δ)
    (tys : HolFiniteMapExact β (List (α × γ)))
    (cExt : HolFiniteMapExact ((α × Option β) × γ) δ)
    (tysExt : HolFiniteMapExact β (List (α × γ)))
    (premises : genvCTysOk c tys ∧ genvCTysOk cExt tysExt ∧
      Disjoint { key | tys.lookup key ≠ none } { key | tysExt.lookup key ≠ none }) :
    genvCTysOk (c.union cExt) (tys.union tysExt) := by
  obtain ⟨left, right, disjoint⟩ := premises
  intro cn tyId arity present
  cases found : c.lookup ((cn, some tyId), arity) with
  | some value =>
    obtain ⟨ctors, table, member⟩ := left cn tyId arity (by simp [found])
    exact ⟨ctors, by simp [HolFiniteMapExact.lookup_union, table], member⟩
  | none =>
    have presentExt : (cExt.lookup ((cn, some tyId), arity)).isSome := by
      simpa [HolFiniteMapExact.lookup_union, found] using present
    obtain ⟨ctors, table, member⟩ := right cn tyId arity presentExt
    have absent : tys.lookup tyId = none := by
      cases old : tys.lookup tyId with
      | none => rfl
      | some oldCtors =>
        have impossible := Set.disjoint_left.mp disjoint (show tyId ∈ { key | tys.lookup key ≠ none } by simp [old])
          (show tyId ∈ { key | tysExt.lookup key ≠ none } by simp [table])
        exact False.elim impossible
    exact ⟨ctors, by simp [HolFiniteMapExact.lookup_union, absent, table], member⟩

/-- Canonical finite-map parameter codec witnesses. -/
theorem holFmapAsFiniteSupportParamWitness_genvCTysOk_extend_c {α β γ δ : Type}
    (c : HolFiniteMapExact ((α × Option β) × γ) δ) :
    GlobalMap.ofBroad (GlobalMap.toBroadlookup c) c.finiteSupport = c := by cases c; rfl

theorem holFmapAsFiniteSupportParamWitness_genvCTysOk_extend_cExt {α β γ δ : Type}
    (cExt : HolFiniteMapExact ((α × Option β) × γ) δ) :
    GlobalMap.ofBroad (GlobalMap.toBroadlookup cExt) cExt.finiteSupport = cExt := by cases cExt; rfl

theorem holFmapAsFiniteSupportParamWitness_genvCTysOk_extend_tys {α β γ : Type}
    (tys : HolFiniteMapExact β (List (α × γ))) :
    GlobalMap.ofBroad (GlobalMap.toBroadlookup tys) tys.finiteSupport = tys := by cases tys; rfl

theorem holFmapAsFiniteSupportParamWitness_genvCTysOk_extend_tysExt {α β γ : Type}
    (tysExt : HolFiniteMapExact β (List (α × γ))) :
    GlobalMap.ofBroad (GlobalMap.toBroadlookup tysExt) tysExt.finiteSupport = tysExt := by cases tysExt; rfl

/-- The nil stamp occurs at exactly its original constructor key. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "genv_lookup_nil"
  (fmap_as_finite_support_parameters := [genvC])]
theorem genvLookupNil (genvC : HolFiniteMapExact ConstructorKey Stamp) (key : ConstructorKey)
    (ok : genvCOk genvC) :
    genvC.lookup key = some (.typeStamp (ofString "[]") listTypeNum) ↔
      key = ((nilTag, some FlatSem.listId), 0) := by
  obtain ⟨cn, arity⟩ := key
  constructor
  · intro h
    have injective := ok.2.2.2.2 cn (nilTag, some FlatSem.listId) arity 0
      (.typeStamp (ofString "[]") listTypeNum) h ok.2.2.1.2
    rcases injective with ⟨rfl, rfl⟩
    rfl
  · intro h
    cases h
    exact ok.2.2.1.2

/-- Flapjack finite-map codec witness; it has no separate HOL declaration. -/
theorem holFmapAsFiniteSupportParamWitness_genvLookupNil_genvC (genvC : HolFiniteMapExact ConstructorKey Stamp) :
    GlobalMap.ofBroad (GlobalMap.toBroadlookup genvC) genvC.finiteSupport = genvC := by cases genvC; rfl

/-- The cons stamp occurs at exactly its original constructor key. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "genv_lookup_cons"
  (fmap_as_finite_support_parameters := [genvC])]
theorem genvLookupCons (genvC : HolFiniteMapExact ConstructorKey Stamp) (key : ConstructorKey)
    (ok : genvCOk genvC) :
    genvC.lookup key = some (.typeStamp (ofString "::") listTypeNum) ↔
      key = ((consTag, some FlatSem.listId), 2) := by
  obtain ⟨cn, arity⟩ := key
  constructor
  · intro h
    have injective := ok.2.2.2.2 cn (consTag, some FlatSem.listId) arity 2
      (.typeStamp (ofString "::") listTypeNum) h ok.2.2.1.1
    rcases injective with ⟨rfl, rfl⟩
    rfl
  · intro h
    cases h
    exact ok.2.2.1.1

/-- Flapjack finite-map codec witness; it has no separate HOL declaration. -/
theorem holFmapAsFiniteSupportParamWitness_genvLookupCons_genvC (genvC : HolFiniteMapExact ConstructorKey Stamp) :
    GlobalMap.ofBroad (GlobalMap.toBroadlookup genvC) genvC.finiteSupport = genvC := by cases genvC; rfl

end Flapjack.Compiler.Backend.SourceToFlat
