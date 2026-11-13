module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ValueRelCases
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.GlobalEnvConditions
public import Flapjack.Compiler.Backend.Semantics.FlatSem.Primitives
public import Flapjack.SemanticPrimitivesHOL.Primitives

@[expose] public section
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.Compiler.Backend.BackendCommon
open Flapjack.Basis.Pure.MlString

namespace PrimitiveTypePort
/-- The global environment has the canonical finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env :=
  GlobalEnv.holFmapAsFiniteSupportWitness env
end PrimitiveTypePort

/-- Primitive type checks are preserved by related values. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "v_rel_check_type"
  (fmap_as_finite_support := [c, tys])]
theorem valueRel_checkType (genv : GlobalEnv)
    (typ : PrimType) (source : SemanticPrimitivesHOL.Value) (flat : FlatSem.Value)
    (premises : ValueRel genv source flat ∧ genvCOk genv.c ∧ SemanticPrimitivesHOL.checkType typ source = true) :
    FlatSem.checkType typ flat = true := by
  obtain ⟨rel, ok, checked⟩ := premises
  cases rel with
  | literal lit =>
    cases typ with
    | wordT size => cases size <;> cases lit <;> simp_all [SemanticPrimitivesHOL.checkType, FlatSem.checkType]
    | _ => cases lit <;> simp_all [SemanticPrimitivesHOL.checkType, FlatSem.checkType]
  | constructor stamp ctor sources flats fields lookup =>
    cases typ <;> try { cases ‹WordSize› } <;> simp_all [SemanticPrimitivesHOL.checkType, FlatSem.checkType]
    cases sources with
    | cons => simp at checked
    | nil =>
      cases fields
      cases stamp with
      | exnStamp => simp at checked
      | typeStamp name num =>
        cases num with
        | succ => simp at checked
        | zero =>
          simp at checked
          rcases checked with h | h
          · subst name
            have hkey := ok.2.2.2.2 ctor (trueTag, some FlatLang.boolId) 0 0
              (.typeStamp (ofString "True") 0) lookup (by simpa [boolTypeNum] using ok.1.1)
            rcases hkey with ⟨rfl, _⟩
            simp
          · subst name
            have hkey := ok.2.2.2.2 ctor (falseTag, some FlatLang.boolId) 0 0
              (.typeStamp (ofString "False") 0) lookup (by simpa [boolTypeNum] using ok.1.2)
            rcases hkey with ⟨rfl, _⟩
            simp
  | tuple => cases typ <;> simp_all [SemanticPrimitivesHOL.checkType]
  | location => cases typ <;> simp_all [SemanticPrimitivesHOL.checkType]
  | vector => cases typ <;> simp_all [SemanticPrimitivesHOL.checkType]
  | closure => cases typ <;> simp_all [SemanticPrimitivesHOL.checkType]
  | recclosure => cases typ <;> simp_all [SemanticPrimitivesHOL.checkType]
  | topRecclosure => cases typ <;> simp_all [SemanticPrimitivesHOL.checkType]
/-- Checked source values relate to their flat conversions. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "check_type_IMP_v_rel"
  (fmap_as_finite_support := [c, tys])]
theorem checked_valueToFlat_related (genv : GlobalEnv) (typ : PrimType)
    (source : SemanticPrimitivesHOL.Value)
    (premises : SemanticPrimitivesHOL.checkType typ source = true ∧ genvCOk genv.c) :
    ValueRel genv source (FlatSem.valueToFlat source) := by
  obtain ⟨checked, ok⟩ := premises
  cases source with
  | litv lit => exact .literal genv lit
  | conv stamp values =>
    cases typ <;> simp_all [SemanticPrimitivesHOL.checkType]
    cases values with
    | cons => simp at checked
    | nil =>
      cases stamp with
      | none => simp at checked
      | some stamp =>
        cases stamp with
        | exnStamp => simp at checked
        | typeStamp name num =>
          cases num with
          | succ => simp at checked
          | zero =>
            simp at checked
            rcases checked with h | h
            · subst name
              simp only [FlatSem.valueToFlat, beq_self_eq_true, ite_true]
              apply ValueRel.constructor
              · exact .nil genv
              · simpa [FlatSem.boolValue, boolToTag, boolTypeNum] using ok.1.1
            · subst name
              simp only [FlatSem.valueToFlat]
              apply ValueRel.constructor
              · exact .nil genv
              · simpa [FlatSem.boolValue, boolToTag, boolTypeNum] using ok.1.2
  | _ => cases typ <;> simp_all [SemanticPrimitivesHOL.checkType]

/-- Converting a related flat value back recovers a checked source value. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "check_type_v_rel_flat_to_v"
  (fmap_as_finite_support := [c, tys])]
theorem checked_flatToValue_related (genv : GlobalEnv) (typ : PrimType)
    (source : SemanticPrimitivesHOL.Value) (flat : FlatSem.Value)
    (premises : SemanticPrimitivesHOL.checkType typ source = true ∧
      ValueRel genv source flat ∧ genvCOk genv.c) : FlatSem.flatToValue flat = source := by
  obtain ⟨checked, rel, ok⟩ := premises
  cases rel with
  | literal lit => rfl
  | constructor stamp ctor sources flats fields lookup =>
    cases typ <;> try { cases ‹WordSize› } <;> simp_all [SemanticPrimitivesHOL.checkType]
    cases sources with
    | cons => simp at checked
    | nil =>
      cases fields
      cases stamp with
      | exnStamp => simp at checked
      | typeStamp name num =>
        cases num with
        | succ => simp at checked
        | zero =>
          simp at checked
          rcases checked with h | h
          · subst name
            have hkey := ok.2.2.2.2 ctor (trueTag, some FlatLang.boolId) 0 0
              (.typeStamp (ofString "True") 0) lookup (by simpa [boolTypeNum] using ok.1.1)
            rcases hkey with ⟨rfl, _⟩
            rfl
          · subst name
            have hkey := ok.2.2.2.2 ctor (falseTag, some FlatLang.boolId) 0 0
              (.typeStamp (ofString "False") 0) lookup (by simpa [boolTypeNum] using ok.1.2)
            rcases hkey with ⟨rfl, _⟩
            rfl
  | tuple => cases typ <;> simp_all [SemanticPrimitivesHOL.checkType]
  | location => cases typ <;> simp_all [SemanticPrimitivesHOL.checkType]
  | vector => cases typ <;> simp_all [SemanticPrimitivesHOL.checkType]
  | closure => cases typ <;> simp_all [SemanticPrimitivesHOL.checkType]
  | recclosure => cases typ <;> simp_all [SemanticPrimitivesHOL.checkType]
  | topRecclosure => cases typ <;> simp_all [SemanticPrimitivesHOL.checkType]
/-- Conversion back to source values preserves a pointwise-related, checked list. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "check_type_v_rel_MAP_flat_to_v"
  (fmap_as_finite_support := [c, tys])]
theorem checked_flatToValue_list (genv : GlobalEnv) (typ : PrimType)
    (xs : List SemanticPrimitivesHOL.Value) (ys : List FlatSem.Value)
    (premises : xs.all (SemanticPrimitivesHOL.checkType typ) = true ∧
      List.Forall₂ (ValueRel genv) xs ys ∧ genvCOk genv.c) :
    ys.map FlatSem.flatToValue = xs := by
  obtain ⟨checked, related, ok⟩ := premises
  induction related with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.all_cons, Bool.and_eq_true] at checked
    simp only [List.map_cons, checked_flatToValue_related genv typ _ _ ⟨checked.1, head, ok⟩,
      ih checked.2]

/-- A source Boolean relates to exactly its corresponding flat Boolean. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "v_rel_Bool_eqn"
  (fmap_as_finite_support := [c, tys])]
theorem boolValueRel_iff (genv : GlobalEnv) (b : Bool) (flat : FlatSem.Value) (ok : genvCOk genv.c) :
    ValueRel genv (SemanticPrimitivesHOL.boolValue b) flat ↔ flat = FlatSem.boolValue b := by
  constructor
  · intro rel
    cases b <;> simp only [SemanticPrimitivesHOL.boolValue, boolTypeNum] at rel
    all_goals
      have shape := ((valueRel_eqns_nonGlobal).2.1 _ flat genv _).mp rel
      simp only [Option.some.injEq, reduceCtorEq, false_and, exists_false, or_false] at shape
      obtain ⟨_, flatCtor, flats, rfl, rfl, fields, lookup⟩ := shape
      cases fields
    · have key := ok.2.2.2.2 flatCtor (falseTag, some FlatLang.boolId) 0 0
        (.typeStamp (ofString "False") 0) lookup (by simpa [boolTypeNum] using ok.1.2)
      rcases key with ⟨rfl, _⟩
      rfl
    · have key := ok.2.2.2.2 flatCtor (trueTag, some FlatLang.boolId) 0 0
        (.typeStamp (ofString "True") 0) lookup (by simpa [boolTypeNum] using ok.1.1)
      rcases key with ⟨rfl, _⟩
      rfl
  · intro h
    subst flat
    cases b <;> apply ValueRel.constructor <;> try exact .nil genv
    · simpa [SemanticPrimitivesHOL.boolValue, FlatSem.boolValue, boolToTag, boolTypeNum] using ok.1.2
    · simpa [SemanticPrimitivesHOL.boolValue, FlatSem.boolValue, boolToTag, boolTypeNum] using ok.1.1

/-- Boolean values and the four built-in exceptions are related. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "v_rel_lems"
  (fmap_as_finite_support := [c, tys])]
theorem valueRel_lemmas (genv : GlobalEnv) (ok : genvCOk genv.c) :
    (∀ b, ValueRel genv (SemanticPrimitivesHOL.boolValue b) (FlatSem.boolValue b)) ∧
    ValueRel genv SemanticPrimitivesHOL.divExnV FlatSem.divExnV ∧
    ValueRel genv SemanticPrimitivesHOL.chrExnV FlatSem.chrExnV ∧
    ValueRel genv SemanticPrimitivesHOL.bindExnV FlatSem.bindExnV ∧
    ValueRel genv SemanticPrimitivesHOL.subExnV FlatSem.subscriptExnV := by
  constructor
  · intro b
    exact (boolValueRel_iff genv b _ ok).mpr rfl
  constructor
  · exact .constructor genv _ _ [] [] (.nil genv) ok.2.1.1
  constructor
  · exact .constructor genv _ _ [] [] (.nil genv) ok.2.1.2.1
  constructor
  · exact .constructor genv _ _ [] [] (.nil genv) ok.2.1.2.2.2
  · exact .constructor genv _ _ [] [] (.nil genv) ok.2.1.2.2.1
end Flapjack.Compiler.Backend.SourceToFlat
