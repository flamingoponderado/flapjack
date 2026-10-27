import Flapjack.Compiler.Backend.SourceToFlat.Proofs.GlobalEnvConditions
import Flapjack.Compiler.Backend.Semantics.FlatSem.PatternMatch

/-! Constructor-map prerequisites for source-to-flat pattern matching. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.SemanticPrimitivesHOL

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
end Flapjack.Compiler.Backend.SourceToFlat
