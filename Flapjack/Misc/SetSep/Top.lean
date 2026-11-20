module

public import Flapjack.Misc.SetSep
@[expose] public section

namespace Flapjack.SetSep
/-- The always-true separation assertion, polymorphic in its input. -/
@[hol "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "SEP_T_def"]
def sepT {α : Type} (_ : α) : Prop := True
end Flapjack.SetSep
