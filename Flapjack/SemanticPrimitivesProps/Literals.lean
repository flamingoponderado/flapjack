import Flapjack.SemanticPrimitivesHOL

/-! Properties of literal type compatibility. -/
namespace Flapjack.SemanticPrimitivesProps
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- Each literal has the same type as itself. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "lit_same_type_refl"]
theorem litSameType_refl (lit : Lit) : litSameType lit lit = true := by
  cases lit <;> rfl

/-- Literal type compatibility is symmetric. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "lit_same_type_sym"]
theorem litSameType_sym (left right : Lit) (same : litSameType left right = true) :
    litSameType right left = true := by
  cases left <;> cases right <;> simp_all [litSameType]

end Flapjack.SemanticPrimitivesProps
