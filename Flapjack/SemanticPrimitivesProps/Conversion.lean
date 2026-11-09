import Flapjack.SemanticPrimitivesHOL.NumericConversion
import Flapjack.SemanticPrimitivesHOL.Primitives

/-! Type preservation for the source primitive conversion. -/
namespace Flapjack.SemanticPrimitivesProps
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- A successful primitive conversion has the requested result type. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "do_conversion_check_type"]
theorem doConversion_checkType (v : Value) (source target : PrimType) (result : Value)
    (converted : doConversion v source target = some (.inr result)) : checkType target result = true := by
  cases source <;> try (rename_i width; cases width)
  all_goals cases target <;> try (rename_i width; cases width)
  all_goals simp [doConversion] at converted
  all_goals try (split at converted <;> simp_all)
  all_goals cases converted <;> rfl

end Flapjack.SemanticPrimitivesProps
