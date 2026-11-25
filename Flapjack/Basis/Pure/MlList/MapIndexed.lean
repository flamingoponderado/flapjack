module

public import Flapjack.HolRef

@[expose] public section

/-!
# Cake `mllist$mapi`

Lean counterpart of `mapi_def` in
`cakeml/basis/pure/mllistScript.sml:364-368`: apply the function to the
element together with its index, counting from `n`.
-/

namespace Flapjack.Basis.Pure.MlList

/-- Original `mapi_def`: map with an index argument.  HOL's `let y = f n h in
y :: ...` is the direct application `f n h :: ...`. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "mapi_def"]
def mapi {α β : Type} (f : Nat → β → α) : Nat → List β → List α
  | _, [] => []
  | n, h :: t => f n h :: mapi f (n + 1) t

end Flapjack.Basis.Pure.MlList
