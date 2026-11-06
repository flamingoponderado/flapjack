module

public import Flapjack.HolRef

@[expose] public section

/-! The option relation from the pinned HOL option theory. -/
namespace Flapjack

/-- The HOL option relation, presented by its four constructor cases. -/
@[hol "hol4/src/coretypes/optionScript.sml" "OPTREL_def"]
def optionRel {A B : Type} (relation : A → B → Prop) : Option A → Option B → Prop
  | none, none => True
  | some left, some right => relation left right
  | _, _ => False

end Flapjack
