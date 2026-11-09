import Flapjack.Compiler.Backend.Semantics.FlatSem.Primitives

namespace Flapjack.Compiler.Backend.FlatToClos

/-- The local HOL operator-proof prerequisite for an integer type check after
conversion from a flat value. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "check_type_IntT_flat_to_v"]
theorem checkTypeInt_flatToValue (v : FlatSem.Value)
    (checked : SemanticPrimitivesHOL.checkType .intT (FlatSem.flatToValue v) = true) :
    ∃ i : Int, v = .litv (.intLit i) := by
  cases v <;> simp [FlatSem.flatToValue, SemanticPrimitivesHOL.checkType] at checked ⊢
  case litv lit => cases lit <;> simp_all
  case conv tag values =>
    cases tag <;> try simp_all
    case some pair =>
      obtain ⟨tag, ty⟩ := pair
      cases ty <;> try simp_all
      case some ty =>
        cases values <;> try simp_all
        split at checked <;> simp_all [SemanticPrimitivesHOL.boolValue]
        all_goals split at * <;> simp_all
        all_goals split at * <;> simp_all

end Flapjack.Compiler.Backend.FlatToClos
