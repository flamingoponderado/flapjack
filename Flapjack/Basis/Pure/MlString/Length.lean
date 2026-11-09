import Flapjack.Basis.Pure.MlString

/-! Length of the faithful HOL `mlstring` carrier. -/
namespace Flapjack.Basis.Pure.MlString.MlString

/-- Count the characters stored in an `mlstring`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "strlen_def"]
def strlen : MlString → Nat
  | .implode chars => chars.length

/-- Exploding an `mlstring` preserves its length. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "LENGTH_explode"]
theorem length_explode (s : MlString) : s.explode.length = strlen s := by
  cases s
  rfl

end Flapjack.Basis.Pure.MlString.MlString
