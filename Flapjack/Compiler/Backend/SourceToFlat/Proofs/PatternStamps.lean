import Flapjack.Compiler.Backend.SourceToFlat.Proofs.GlobalEnvConditions
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.StateRel
import Flapjack.Compiler.Backend.Semantics.FlatSem.PatternMatch

/-! Constructor-map prerequisites for source-to-flat pattern matching. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.SemanticPrimitivesHOL

/-- Every optional constructor identifier has the same type as itself. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "ctor_same_type_refl"]
theorem ctorSameType_refl {α β : Type} (x : Option (α × β)) :
    FlatSem.ctorSameType x x := by
  cases x with
  | none => trivial
  | some pair => cases pair; rfl

/-- Two present constructor identifiers have the same type exactly when their
type components agree. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "ctor_same_type_SND"]
theorem ctorSameType_some_iff {α β γ : Type} (x : α × β) (y : γ × β) :
    FlatSem.ctorSameType (some x) (some y) ↔ x.2 = y.2 := by
  cases x
  cases y
  rfl

/-- Mapping the second component of a pair preserves its first component. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "FST_PAIR_MAP_I"]
theorem fst_pairMap_id {α β γ : Type} (f : β → γ) (pair : α × β) :
    (Prod.map id f pair).1 = pair.1 := by
  cases pair
  rfl

/-- Equal flat constructor IDs and arities determine the same source constructor. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml"
  "genv_c_ok_same_type_FST_eq_imp_same_ctor" (fmap_as_finite_support_parameters := [genvC])]
theorem genvCOk_sameType_ctorEq (genvC : HolFiniteMapExact ConstructorKey Stamp)
    (cn1 cn2 : FlatLang.CtorId × FlatLang.TypeId) (l1 l2 : Nat) (s1 s2 : Stamp)
    (ok : genvCOk genvC) (lookup1 : genvC.lookup (cn1, l1) = some s1)
    (lookup2 : genvC.lookup (cn2, l2) = some s2) (same : sameType s1 s2 = true)
    (first : cn1.1 = cn2.1) (length : l1 = l2) : sameCtor s1 s2 = true := by
  have typeSame : FlatSem.ctorSameType (some cn1) (some cn2) :=
    (ok.2.2.2.1 cn1 cn2 l1 l2 s1 s2 lookup1 lookup2).mp (by simpa [ctorSameType] using same)
  have second : cn1.2 = cn2.2 := by simpa [FlatSem.ctorSameType] using typeSame
  have cnEq : cn1 = cn2 := Prod.ext first second
  subst cn2
  subst l2
  have stamps : s1 = s2 := Option.some.inj (lookup1.symm.trans lookup2)
  subst s2
  simp [sameCtor]

private def StampMap.toBroadlookup (m : HolFiniteMapExact ConstructorKey Stamp) := m.lookup
private def StampMap.ofBroad (lookup : ConstructorKey → Option Stamp)
    (support : ∃ keys : List ConstructorKey, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact ConstructorKey Stamp := ⟨lookup, support⟩

/-- Flapjack-specific finite-map codec witness. -/
theorem holFmapAsFiniteSupportParamWitness_genvCOk_sameType_ctorEq_genvC
    (genvC : HolFiniteMapExact ConstructorKey Stamp) :
    StampMap.ofBroad (StampMap.toBroadlookup genvC) genvC.finiteSupport = genvC := by
  cases genvC
  rfl

/-- Flapjack infrastructure: a stronger stamp-compatibility prerequisite that
does not require the original theorem's state or namespace assumptions. -/
theorem genvCOk_pmatchStamps (genvC : HolFiniteMapExact ConstructorKey Stamp)
    (genvTys : HolFiniteMapExact Nat TypeConstructors) (flatCn : FlatLang.CtorId)
    (group : FlatLang.TypeGroupId) (flatStamp : FlatLang.CtorId × FlatLang.TypeId)
    (l l' : Nat) (src src' : Stamp)
    (ok : genvCOk genvC) (typesOk : genvCTysOk genvC genvTys)
    (same : sameType src src' = true)
    (lookup1 : genvC.lookup ((flatCn, group.map Prod.fst), l) = some src)
    (lookup2 : genvC.lookup (flatStamp, l') = some src')
    (groupLookup : ∀ ty constructors, group = some (ty, constructors) →
      genvTys.lookup ty = some constructors) :
    FlatSem.PmatchStampsOk (some (flatCn, group)) (some flatStamp) l l' := by
  have typeSame : FlatSem.ctorSameType (some (flatCn, group.map Prod.fst)) (some flatStamp) :=
    (ok.2.2.2.1 (flatCn, group.map Prod.fst) flatStamp l l' src src' lookup1 lookup2).mp
      (by simpa [ctorSameType] using same)
  have typeEq : group.map Prod.fst = flatStamp.2 := by simpa [FlatSem.ctorSameType] using typeSame
  obtain ⟨cn', tid⟩ := flatStamp
  cases group with
  | none =>
    simp at typeEq
    subst tid
    exact .exception flatCn cn' l l'
  | some group =>
    obtain ⟨ty, ctors⟩ := group
    simp at typeEq
    subst tid
    have firstPresent : (genvC.lookup ((flatCn, some ty), l)).isSome = true := by
      change (genvC.lookup ((flatCn, (some (ty, ctors)).map Prod.fst), l)).isSome = true
      rw [lookup1]
      rfl
    have secondPresent : (genvC.lookup ((cn', some ty), l')).isSome = true := by
      change (genvC.lookup ((cn', (some (ty, ctors)).map Prod.fst), l')).isSome = true
      rw [lookup2]
      rfl
    obtain ⟨cs1, get1, member1⟩ := typesOk flatCn ty l firstPresent
    obtain ⟨cs2, get2, member2⟩ := typesOk cn' ty l' secondPresent
    have desired := groupLookup ty ctors rfl
    have eq1 : cs1 = ctors := Option.some.inj (get1.symm.trans desired)
    have eq2 : cs2 = ctors := Option.some.inj (get2.symm.trans desired)
    subst cs1
    subst cs2
    exact .constructor flatCn cn' ty ty ctors l l' rfl member1 member2

namespace PatternStampsPort
/-- The global environment has the canonical finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env :=
  GlobalEnv.holFmapAsFiniteSupportWitness env
end PatternStampsPort

@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "genv_c_ok_pmatch_stamps_ok"
  (fmap_as_finite_support := [c, tys])]
theorem genvCOk_pmatchStamps_source {C F M N : Type} (genv : GlobalEnv)
    (source : SemanticPrimitivesHOL.State F) (target : FlatSem.State C F)
    (compMap : Flapjack.NamespaceHOL.Namespace M N (FlatLang.CtorId × FlatLang.TypeGroupId))
    (name : Flapjack.NamespaceHOL.Ident M N) (flatCn : FlatLang.CtorId)
    (group : FlatLang.TypeGroupId) (flatStamp : FlatLang.CtorId × FlatLang.TypeId)
    (l l' : Nat) (src src' : Stamp)
    (premises : StateRel genv source target ∧
      @Flapjack.NamespaceHOL.nsLookup M N _ (Classical.decEq M) (Classical.decEq N) compMap name = some (flatCn, group) ∧
      sameType src src' = true ∧ genvCOk genv.c ∧ genvCTysOk genv.c genv.tys ∧
      genv.c.lookup ((flatCn, group.map Prod.fst), l) = some src ∧
      genv.c.lookup (flatStamp, l') = some src' ∧
      (∀ ty constructors, group = some (ty, constructors) → genv.tys.lookup ty = some constructors)) :
    FlatSem.PmatchStampsOk (some (flatCn, group)) (some flatStamp) l l' := by
  obtain ⟨_, _, same, ok, typesOk, lookup1, lookup2, groupLookup⟩ := premises
  exact genvCOk_pmatchStamps genv.c genv.tys flatCn group flatStamp l l' src src'
    ok typesOk same lookup1 lookup2 groupLookup
end Flapjack.Compiler.Backend.SourceToFlat
