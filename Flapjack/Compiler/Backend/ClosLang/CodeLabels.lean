module

public import Flapjack.Compiler.Backend.ClosLang.Syntax
public import Mathlib.Data.Set.Basic

@[expose] public section

/-! Code labels referenced by closure-language primitive assignments. -/
namespace Flapjack.Compiler.Backend.ClosLang

@[hol "cakeml/compiler/backend/closLangScript.sml" "assign_get_code_label_def"]
def assignGetCodeLabel : Op → Set Nat
  | .label label => {label}
  | _ => ∅

end Flapjack.Compiler.Backend.ClosLang
