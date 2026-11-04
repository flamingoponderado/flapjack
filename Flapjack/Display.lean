import Flapjack.Pancake.PanLang
import Flapjack.Pancake.CrepLang
import Flapjack.Pancake.LoopLang
import Flapjack.NumSet

/-!
The small display-language boundary used by Pancake's pass printer.

This is the Lean counterpart of `displayLang$sExp` and the basic helpers in
`presLangScript.sml`.  Keeping the trace parameter explicit preserves the
shape of Cake's `Item (trace option) name children`, even though the first
ported Pancake helpers below all use `NONE`.
-/

namespace Flapjack

/-! The small string-tree and pretty intermediate languages used by Cake's
    `display_to_str_tree`/`str_tree_to_strs` boundary. -/

def varKindToDisplayString : VarKind → String
  := varKindToString

/-! The typed output-boundary counterpart of Cake's `any_pan_prog_pp_def`
    (`pan_passesScript.sml:660-666`).  Backend Cake stages are represented by
    their already-rendered string stream because the source/backend ASTs are
    not part of Flapjack's source-shaped language. -/

def destAnnot (program : Prog α) : Option (String × String) :=
  match program with
  | .annot tag text => some (tag, text)
  | _ => none

end Flapjack
