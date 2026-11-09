import Flapjack.HolRef

namespace Flapjack.Compiler.Backend.BackendCommon

/-- The source range for integers represented directly in BVI. -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "small_enough_int_def"]
def smallEnoughInt (value : Int) : Prop := -268435457 ≤ value ∧ value ≤ 268435457

instance (value : Int) : Decidable (smallEnoughInt value) := inferInstanceAs (Decidable (_ ∧ _))

end Flapjack.Compiler.Backend.BackendCommon
