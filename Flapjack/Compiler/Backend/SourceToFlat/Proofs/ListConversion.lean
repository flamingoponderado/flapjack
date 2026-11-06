import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ValueRelCases
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.GlobalEnvConditions
import Flapjack.Compiler.Backend.Semantics.FlatSem.Conversions
import Flapjack.SemanticPrimitivesHOL.Conversions

/-! List conversion compatibility over the factored source-to-flat relation.
The relation's full correspondence to HOL remains open. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendCommon
open Flapjack.Basis.Pure.MlString

/-- Related lists encode to related source and flat list values when the
constructor map contains the list stamps. This is Flapjack infrastructure
over the factored relation, not a tagged HOL theorem. -/
theorem listToValue_related (genv : GlobalEnv) (hasLists : hasLists genv.c)
    (xs : List SemanticPrimitivesHOL.Value) (ys : List FlatSem.Value)
    (related : List.Forall₂ (ValueRel genv) xs ys) :
    ValueRel genv (SemanticPrimitivesHOL.listToValue xs) (FlatSem.listToValue ys) := by
  induction related with
  | nil =>
    apply ValueRel.constructor
    · exact .nil genv
    · exact hasLists.2
  | cons head tail ih =>
    apply ValueRel.constructor
    · exact .cons genv _ _ _ _ head (.cons genv _ _ _ _ ih (.nil genv))
    · exact hasLists.1

/-- Concatenating related lists of values gives the same optional string.
This is Flapjack infrastructure over the factored relation. -/
theorem valuesToString_related (genv : GlobalEnv)
    (xs : List SemanticPrimitivesHOL.Value) (ys : List FlatSem.Value)
    (related : List.Forall₂ (ValueRel genv) xs ys) :
    SemanticPrimitivesHOL.valuesToString xs = FlatSem.valuesToString ys := by
  induction related with
  | nil => rfl
  | cons head tail ih =>
    cases head <;> try (rfl)
    case literal lit => cases lit <;> simp [SemanticPrimitivesHOL.valuesToString, FlatSem.valuesToString, ih]

/-- Successful source-list decoding is preserved by related flat values.
This is infrastructure over the factored relation, whose HOL correspondence remains open. -/
theorem valueToList_related (genv : GlobalEnv) (ok : genvCOk genv.c)
    (source : SemanticPrimitivesHOL.Value) (flat : FlatSem.Value)
    (xs : List SemanticPrimitivesHOL.Value)
    (rel : ValueRel genv source flat) (decoded : SemanticPrimitivesHOL.valueToList source = some xs) :
    ∃ ys, FlatSem.valueToList flat = some ys ∧ List.Forall₂ (ValueRel genv) xs ys := by
  induction source using SemanticPrimitivesHOL.valueToList.induct generalizing flat xs with
  | case1 =>
    simp [SemanticPrimitivesHOL.valueToList] at decoded
    subst xs
    obtain ⟨flats, ctor, hfields, rfl, flatCtor, rfl, lookup⟩ :=
      (valueRel_conv_iff genv _ _ flat).mp rel
    have hc := (genvLookupNil genv.c (flatCtor, 0) ok).mp lookup
    cases hc
    cases hfields
    exact ⟨[], by simp [FlatSem.valueToList], .nil⟩
  | case2 stamp ne => simp [SemanticPrimitivesHOL.valueToList, ne] at decoded
  | case3 head tail ih =>
    simp only [SemanticPrimitivesHOL.valueToList, if_true] at decoded
    obtain ⟨flats, ctor, hfields, rfl, flatCtor, rfl, lookup⟩ :=
      (valueRel_conv_iff genv _ _ flat).mp rel
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

/-- Successful source-character-list decoding is preserved by related flat values.
This is infrastructure over the factored relation, whose HOL correspondence remains open. -/
theorem valueToCharList_related (genv : GlobalEnv) (ok : genvCOk genv.c)
    (source : SemanticPrimitivesHOL.Value) (flat : FlatSem.Value)
    (xs : List HolChar)
    (rel : ValueRel genv source flat) (decoded : SemanticPrimitivesHOL.valueToCharList source = some xs) :
    FlatSem.valueToCharList flat = some xs := by
  induction source using SemanticPrimitivesHOL.valueToCharList.induct generalizing flat xs with
  | case1 =>
    simp [SemanticPrimitivesHOL.valueToCharList] at decoded
    subst xs
    obtain ⟨flats, ctor, hfields, rfl, flatCtor, rfl, lookup⟩ :=
      (valueRel_conv_iff genv _ _ flat).mp rel
    have hc := (genvLookupNil genv.c (flatCtor, 0) ok).mp lookup
    cases hc
    cases hfields
    simp [FlatSem.valueToCharList]
  | case2 stamp ne => simp [SemanticPrimitivesHOL.valueToCharList, ne] at decoded
  | case3 head tail ih =>
    simp only [SemanticPrimitivesHOL.valueToCharList, if_true] at decoded
    obtain ⟨flats, ctor, hfields, rfl, flatCtor, rfl, lookup⟩ :=
      (valueRel_conv_iff genv _ _ flat).mp rel
    have hc := (genvLookupCons genv.c (flatCtor, 2) ok).mp lookup
    cases hc
    cases hfields with
    | cons headRel tailRel =>
      cases tailRel with
      | cons tailRel nilRel =>
        cases nilRel
        have hhead := (valueRel_literal_iff genv (.char head) _).mp headRel
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
