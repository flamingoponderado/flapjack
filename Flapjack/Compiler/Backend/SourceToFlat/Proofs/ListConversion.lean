module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ValueRelCases
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.GlobalEnvConditions
public import Flapjack.Compiler.Backend.Semantics.FlatSem.Conversions
public import Flapjack.SemanticPrimitivesHOL.Conversions

@[expose] public section

/-! List conversion compatibility over the source-to-flat value relation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendCommon
open Flapjack.Basis.Pure.MlString

namespace ListConversionPort
/-- Canonical global finite-map carrier roundtrip. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env
end ListConversionPort

/-- Related lists encode to related source and flat list values when the
constructor map contains the list stamps. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "list_to_v_v_rel"
  (fmap_as_finite_support := [c, tys])]
theorem listToValue_related (genv : GlobalEnv)
    (xs : List SemanticPrimitivesHOL.Value) (ys : List FlatSem.Value)
    (premises : hasLists genv.c ∧ List.Forall₂ (ValueRel genv) xs ys) :
    ValueRel genv (SemanticPrimitivesHOL.listToValue xs) (FlatSem.listToValue ys) := by
  obtain ⟨hasLists, related⟩ := premises
  induction related with
  | nil =>
    apply ValueRel.constructor
    · exact .nil genv
    · exact hasLists.2
  | cons head tail ih =>
    apply ValueRel.constructor
    · exact .cons genv _ _ _ _ head (.cons genv _ _ _ _ ih (.nil genv))
    · exact hasLists.1

/-- Related lists preserve successful string decoding. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "vs_to_string"
  (fmap_as_finite_support := [c, tys])]
theorem valuesToString_related (genv : GlobalEnv)
    (xs : List SemanticPrimitivesHOL.Value) (ys : List FlatSem.Value) (value : MlString)
    (related : List.Forall₂ (ValueRel genv) xs ys)
    (decoded : SemanticPrimitivesHOL.valuesToString xs = some value) :
    FlatSem.valuesToString ys = some value := by
  have same : SemanticPrimitivesHOL.valuesToString xs = FlatSem.valuesToString ys := by
    clear decoded
    induction related with
    | nil => rfl
    | cons head tail ih =>
      cases head <;> try (rfl)
      case literal lit => cases lit <;> simp [SemanticPrimitivesHOL.valuesToString, FlatSem.valuesToString, ih]
  rw [← same]
  exact decoded

/-- Successful source-list decoding is preserved by related flat values. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "v_to_list"
  (fmap_as_finite_support := [c, tys])]
theorem valueToList_related (genv : GlobalEnv) (ok : genvCOk genv.c)
    (source : SemanticPrimitivesHOL.Value) (flat : FlatSem.Value)
    (xs : List SemanticPrimitivesHOL.Value)
    (premises : ValueRel genv source flat ∧ SemanticPrimitivesHOL.valueToList source = some xs) :
    ∃ ys, FlatSem.valueToList flat = some ys ∧ List.Forall₂ (ValueRel genv) xs ys := by
  obtain ⟨rel, decoded⟩ := premises
  induction source using SemanticPrimitivesHOL.valueToList.induct generalizing flat xs with
  | case1 =>
    simp [SemanticPrimitivesHOL.valueToList] at decoded
    subst xs
    have shape := ((valueRel_eqns_nonGlobal).2.1 _ flat genv _).mp rel
    simp only [Option.some.injEq, reduceCtorEq, false_and, exists_false, or_false] at shape
    obtain ⟨_, flatCtor, flats, rfl, rfl, hfields, lookup⟩ := shape
    have hc := (genvLookupNil genv.c (flatCtor, 0) ok).mp lookup
    cases hc
    cases hfields
    exact ⟨[], by simp [FlatSem.valueToList], .nil⟩
  | case2 stamp ne => simp [SemanticPrimitivesHOL.valueToList, ne] at decoded
  | case3 head tail ih =>
    simp only [SemanticPrimitivesHOL.valueToList, if_true] at decoded
    have shape := ((valueRel_eqns_nonGlobal).2.1 _ flat genv _).mp rel
    simp only [Option.some.injEq, reduceCtorEq, false_and, exists_false, or_false] at shape
    obtain ⟨_, flatCtor, flats, rfl, rfl, hfields, lookup⟩ := shape
    have hc := (genvLookupCons genv.c (flatCtor, 2) ok).mp lookup
    cases hc
    cases hfields with
    | cons headRel tailRel =>
      cases tailRel with
      | cons tailRel nilRel =>
        cases nilRel
        cases hv : SemanticPrimitivesHOL.valueToList tail with
        | none => simp [hv] at decoded
        | some rest =>
          simp [hv] at decoded
          subst xs
          obtain ⟨ys, hy, hry⟩ := ih _ _ tailRel hv
          exact ⟨_, by simp [FlatSem.valueToList, hy], .cons headRel hry⟩
  | case4 stamp head tail ne => simp [SemanticPrimitivesHOL.valueToList, ne] at decoded
  | case5 source hnil hcons =>
    simp only [SemanticPrimitivesHOL.valueToList] at decoded
    simp at decoded

/-- Successful source-character-list decoding is preserved by related flat values. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "v_to_char_list"
  (fmap_as_finite_support := [c, tys])]
theorem valueToCharList_related (genv : GlobalEnv) (ok : genvCOk genv.c)
    (source : SemanticPrimitivesHOL.Value) (flat : FlatSem.Value)
    (xs : List HolChar)
    (premises : ValueRel genv source flat ∧ SemanticPrimitivesHOL.valueToCharList source = some xs) :
    FlatSem.valueToCharList flat = some xs := by
  obtain ⟨rel, decoded⟩ := premises
  induction source using SemanticPrimitivesHOL.valueToCharList.induct generalizing flat xs with
  | case1 =>
    simp [SemanticPrimitivesHOL.valueToCharList] at decoded
    subst xs
    have shape := ((valueRel_eqns_nonGlobal).2.1 _ flat genv _).mp rel
    simp only [Option.some.injEq, reduceCtorEq, false_and, exists_false, or_false] at shape
    obtain ⟨_, flatCtor, flats, rfl, rfl, hfields, lookup⟩ := shape
    have hc := (genvLookupNil genv.c (flatCtor, 0) ok).mp lookup
    cases hc
    cases hfields
    simp [FlatSem.valueToCharList]
  | case2 stamp ne => simp [SemanticPrimitivesHOL.valueToCharList, ne] at decoded
  | case3 head tail ih =>
    simp only [SemanticPrimitivesHOL.valueToCharList, if_true] at decoded
    have shape := ((valueRel_eqns_nonGlobal).2.1 _ flat genv _).mp rel
    simp only [Option.some.injEq, reduceCtorEq, false_and, exists_false, or_false] at shape
    obtain ⟨_, flatCtor, flats, rfl, rfl, hfields, lookup⟩ := shape
    have hc := (genvLookupCons genv.c (flatCtor, 2) ok).mp lookup
    cases hc
    cases hfields with
    | cons headRel tailRel =>
      cases tailRel with
      | cons tailRel nilRel =>
        cases nilRel
        have hhead := ((valueRel_eqns_nonGlobal).1 _ (.char head) genv).mp headRel
        cases hhead
        cases hv : SemanticPrimitivesHOL.valueToCharList tail with
        | none => simp [hv] at decoded
        | some rest =>
          simp [hv] at decoded
          subst xs
          have hy := ih _ _ tailRel hv
          simp [FlatSem.valueToCharList, hy]
  | case4 stamp head tail ne => simp [SemanticPrimitivesHOL.valueToCharList, ne] at decoded
  | case5 source hnil hcons =>
    simp only [SemanticPrimitivesHOL.valueToCharList] at decoded
    simp at decoded
end Flapjack.Compiler.Backend.SourceToFlat
