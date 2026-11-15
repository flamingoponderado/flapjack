module

public import Flapjack.HolRef

@[expose] public section

/-! Environment lookup for BVL variable lists. -/
namespace Flapjack.Compiler.Backend.BvlProps

/-- Look up each variable index in order, failing if any index is out of range. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "get_vars_def"]
def getVars {α : Type} : List Nat → List α → Option (List α)
  | [], _ => some []
  | index :: rest, env =>
    match env[index]? with
    | none => none
    | some value => (getVars rest env).map (value :: ·)

end Flapjack.Compiler.Backend.BvlProps
