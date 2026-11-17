module

public import Flapjack.Compiler.Inference.Unify.WorklistBag
public import Flapjack.Compiler.Inference.Unify

@[expose] public section

/-! The original normalization worklist's continuation and item bags. -/
namespace Flapjack.Compiler.Inference.Unify

@[hol "cakeml/compiler/inference/unifyScript.sml" "star_kwork_def"]
noncomputable def starKwork : List KclKont → Bag InferT
  | [] => emptyBag
  | .cons items _ :: rest => bagUnion (bagOfList items) (starKwork rest)
  | _ :: rest => starKwork rest

@[hol "cakeml/compiler/inference/unifyScript.sml" "star_workbag_def"]
noncomputable def starWorkbag (ready : Bool) (items : List InferT) (kont : List KclKont) : Bag InferT :=
  if ready then starKwork kont else bagUnion (bagOfList items) (starKwork kont)

@[hol "cakeml/compiler/inference/unifyScript.sml" "FINITE_star_kwork"]
theorem finiteStarKwork (kont : List KclKont) : finiteBag (starKwork kont) := by
  induction kont with
  | nil => exact finiteEmptyBag
  | cons frame rest ih =>
    cases frame with
    | db _ | app _ _ | uv _ => exact ih
    | cons items _ =>
      exact finiteBagUnion _ (finiteBagOfList items) _ ih

@[hol "cakeml/compiler/inference/unifyScript.sml" "FINITE_star_workbag"]
theorem finiteStarWorkbag (ready : Bool) (items : List InferT) (kont : List KclKont) :
    finiteBag (starWorkbag ready items kont) := by
  cases ready with
  | false =>
    exact finiteBagUnion _ (finiteBagOfList items) _ (finiteStarKwork kont)
  | true => exact finiteStarKwork kont

@[hol "cakeml/compiler/inference/unifyScript.sml" "isCONSk_def"]
def isConsK : KclKont → Bool
  | .cons _ _ => true
  | _ => false

end Flapjack.Compiler.Inference.Unify
