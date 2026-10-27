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
end Flapjack.Compiler.Backend.SourceToFlat
