import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ValueRelCases
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.GlobalEnvConditions
import Flapjack.Compiler.Backend.Semantics.FlatSem.Primitives
import Flapjack.SemanticPrimitivesHOL.Primitives
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.Compiler.Backend.BackendCommon
open Flapjack.Basis.Pure.MlString

/-- Primitive type checks are preserved by related values. This is infrastructure
over the factored relation, whose full HOL correspondence remains open. -/
theorem valueRel_checkType (genv : GlobalEnv) (ok : genvCOk genv.c)
    (typ : PrimType) (source : SemanticPrimitivesHOL.Value) (flat : FlatSem.Value)
    (rel : ValueRel genv source flat) (checked : SemanticPrimitivesHOL.checkType typ source = true) :
    FlatSem.checkType typ flat = true := by
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
/-- Checked source values relate to their flat conversions. This is infrastructure
over the factored relation, whose full HOL correspondence remains open. -/
theorem checked_valueToFlat_related (genv : GlobalEnv) (ok : genvCOk genv.c)
    (typ : PrimType) (source : SemanticPrimitivesHOL.Value)
    (checked : SemanticPrimitivesHOL.checkType typ source = true) :
    ValueRel genv source (FlatSem.valueToFlat source) := by
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
              simp only [FlatSem.valueToFlat, beq_self_eq_true, if_true]
              apply ValueRel.constructor
              · exact .nil genv
              · simpa [FlatSem.boolValue, boolToTag, boolTypeNum] using ok.1.1
            · subst name
              simp only [FlatSem.valueToFlat]
              apply ValueRel.constructor
              · exact .nil genv
              · simpa [FlatSem.boolValue, boolToTag, boolTypeNum] using ok.1.2
  | _ => cases typ <;> simp_all [SemanticPrimitivesHOL.checkType]

/-- Converting a related flat value back recovers a checked source value. This is
infrastructure over the factored relation, whose full HOL correspondence remains open. -/
theorem checked_flatToValue_related (genv : GlobalEnv) (ok : genvCOk genv.c)
    (typ : PrimType) (source : SemanticPrimitivesHOL.Value) (flat : FlatSem.Value)
    (checked : SemanticPrimitivesHOL.checkType typ source = true)
    (rel : ValueRel genv source flat) : FlatSem.flatToValue flat = source := by
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
/-- Conversion back to source values preserves a pointwise-related, checked list.
This is infrastructure over the factored relation, whose HOL correspondence remains open. -/
theorem checked_flatToValue_list (genv : GlobalEnv) (ok : genvCOk genv.c)
    (typ : PrimType) (xs : List SemanticPrimitivesHOL.Value) (ys : List FlatSem.Value)
    (checked : xs.all (SemanticPrimitivesHOL.checkType typ) = true)
    (related : List.Forall₂ (ValueRel genv) xs ys) :
    ys.map FlatSem.flatToValue = xs := by
  induction related with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.all_cons, Bool.and_eq_true] at checked
    simp only [List.map_cons, checked_flatToValue_related genv ok typ _ _ checked.1 head,
      ih checked.2]

/-- Related Boolean constructors under the original constructor-map assumptions.
This is infrastructure over the factored relation. -/
theorem boolValue_related (genv : GlobalEnv) (ok : genvCOk genv.c) (b : Bool) :
    ValueRel genv (SemanticPrimitivesHOL.boolValue b) (FlatSem.boolValue b) := by
  cases b <;> apply ValueRel.constructor <;> try exact .nil genv
  · simpa [SemanticPrimitivesHOL.boolValue, FlatSem.boolValue, boolToTag, boolTypeNum] using ok.1.2
  · simpa [SemanticPrimitivesHOL.boolValue, FlatSem.boolValue, boolToTag, boolTypeNum] using ok.1.1

/-- Related original exception constructors under the constructor-map assumptions.
This is infrastructure over the factored relation. -/
theorem exceptionValues_related (genv : GlobalEnv) (ok : genvCOk genv.c) :
    ValueRel genv SemanticPrimitivesHOL.divExnV FlatSem.divExnV ∧
    ValueRel genv SemanticPrimitivesHOL.chrExnV FlatSem.chrExnV ∧
    ValueRel genv SemanticPrimitivesHOL.bindExnV FlatSem.bindExnV ∧
    ValueRel genv SemanticPrimitivesHOL.subExnV FlatSem.subscriptExnV := by
  constructor
  · exact .constructor genv _ _ [] [] (.nil genv) ok.2.1.1
  constructor
  · exact .constructor genv _ _ [] [] (.nil genv) ok.2.1.2.1
  constructor
  · exact .constructor genv _ _ [] [] (.nil genv) ok.2.1.2.2.2
  · exact .constructor genv _ _ [] [] (.nil genv) ok.2.1.2.2.1
end Flapjack.Compiler.Backend.SourceToFlat
