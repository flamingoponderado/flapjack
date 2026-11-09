module

public import Flapjack.Compiler.Backend.Semantics.FlatSem.Primitives

@[expose] public section

namespace Flapjack.Compiler.Backend.FlatToClos

/-- Literal outputs of the flat-to-source value conversion come from the same
flat literal. This proof helper supports the original type-check lemmas below;
it is not a separately named HOL declaration. -/
private theorem flatToValue_lit_inv (v : FlatSem.Value) (l : AstHOL.Lit)
    (h : FlatSem.flatToValue v = .litv l) : v = .litv l := by
  cases v <;> simp [FlatSem.flatToValue] at h ⊢
  case litv lit => exact h
  case conv tag values =>
    cases tag <;> try simp_all
    case some pair =>
      obtain ⟨tag, ty⟩ := pair
      cases ty <;> try simp_all
      case some ty =>
        cases values <;> try simp_all
        split at h <;> simp_all [SemanticPrimitivesHOL.boolValue]
        all_goals split at * <;> simp_all

/-- The local HOL operator-proof prerequisite for an integer type check after
conversion from a flat value. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "check_type_IntT_flat_to_v"]
theorem checkTypeInt_flatToValue (v : FlatSem.Value)
    (checked : SemanticPrimitivesHOL.checkType .intT (FlatSem.flatToValue v) = true) :
    ∃ i : Int, v = .litv (.intLit i) := by
  cases h : FlatSem.flatToValue v <;> simp [h, SemanticPrimitivesHOL.checkType] at checked
  case litv lit =>
    cases lit <;> simp at checked
    case intLit i => exact ⟨i, flatToValue_lit_inv v _ h⟩

/-- The local HOL prerequisite for a 64-bit floating literal. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "check_type_Float64T_flat_to_v"]
theorem checkTypeFloat64_flatToValue (v : FlatSem.Value)
    (checked : SemanticPrimitivesHOL.checkType .float64T (FlatSem.flatToValue v) = true) :
    ∃ w : BitVec 64, v = .litv (.float64 w) := by
  cases h : FlatSem.flatToValue v <;> simp [h, SemanticPrimitivesHOL.checkType] at checked
  case litv lit =>
    cases lit <;> simp at checked
    case float64 w => exact ⟨w, flatToValue_lit_inv v _ h⟩

/-- The local HOL prerequisite for an 8-bit word literal. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "check_type_WordT_W8_flat_to_v"]
theorem checkTypeWord8_flatToValue (v : FlatSem.Value)
    (checked : SemanticPrimitivesHOL.checkType (.wordT .w8) (FlatSem.flatToValue v) = true) :
    ∃ w : BitVec 8, v = .litv (.word8 w) := by
  cases h : FlatSem.flatToValue v <;> simp [h, SemanticPrimitivesHOL.checkType] at checked
  case litv lit =>
    cases lit <;> simp at checked
    case word8 w => exact ⟨w, flatToValue_lit_inv v _ h⟩

/-- The local HOL prerequisite for a 64-bit word literal. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "check_type_WordT_W64_flat_to_v"]
theorem checkTypeWord64_flatToValue (v : FlatSem.Value)
    (checked : SemanticPrimitivesHOL.checkType (.wordT .w64) (FlatSem.flatToValue v) = true) :
    ∃ w : BitVec 64, v = .litv (.word64 w) := by
  cases h : FlatSem.flatToValue v <;> simp [h, SemanticPrimitivesHOL.checkType] at checked
  case litv lit =>
    cases lit <;> simp at checked
    case word64 w => exact ⟨w, flatToValue_lit_inv v _ h⟩

/-- The local HOL prerequisite for a character literal. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "check_type_CharT_flat_to_v"]
theorem checkTypeChar_flatToValue (v : FlatSem.Value)
    (checked : SemanticPrimitivesHOL.checkType .charT (FlatSem.flatToValue v) = true) :
    ∃ c : Basis.Pure.MlString.HolChar, v = .litv (.char c) := by
  cases h : FlatSem.flatToValue v <;> simp [h, SemanticPrimitivesHOL.checkType] at checked
  case litv lit =>
    cases lit <;> simp at checked
    case char c => exact ⟨c, flatToValue_lit_inv v _ h⟩

/-- The local HOL Boolean check concludes with the original two alternatives. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "check_type_BoolT_flat_to_v"]
theorem checkTypeBool_flatToValue (v : FlatSem.Value)
    (checked : SemanticPrimitivesHOL.checkType .boolT (FlatSem.flatToValue v) = true) :
    v = FlatSem.boolValue false ∨ v = FlatSem.boolValue true := by
  cases v <;> simp [FlatSem.flatToValue, SemanticPrimitivesHOL.checkType] at checked ⊢
  case conv tag values =>
    cases tag <;> try simp_all
    case some pair =>
      obtain ⟨tag, ty⟩ := pair
      cases ty <;> try simp_all
      case some ty =>
        cases values <;> try simp_all
        simp [FlatSem.boolValue, FlatLang.boolId, BackendCommon.trueTag,
          BackendCommon.falseTag, SemanticPrimitivesHOL.boolValue] at checked ⊢
        by_cases first : ty = 0 ∧ tag = 1
        · obtain ⟨rfl, rfl⟩ := first
          simp [BackendCommon.boolToTag, BackendCommon.trueTag, BackendCommon.falseTag]
        · by_cases second : ty = 0 ∧ tag = 0
          · obtain ⟨rfl, rfl⟩ := second
            simp [BackendCommon.boolToTag, BackendCommon.trueTag, BackendCommon.falseTag]
          · simp [first, second] at checked

end Flapjack.Compiler.Backend.FlatToClos
