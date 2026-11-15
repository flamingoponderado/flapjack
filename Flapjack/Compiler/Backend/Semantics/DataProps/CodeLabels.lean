module

public import Flapjack.Compiler.Backend.ClosLang.CodeLabels
public import Flapjack.Compiler.Backend.DataLang.Syntax

@[expose] public section

/-! Code labels referenced by data-language programs. -/
namespace Flapjack.Compiler.Backend.DataSem

@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "get_code_labels_def"]
def getCodeLabels : DataLang.Prog → Set Nat
  | .call _ destination _ handler =>
      (match destination with | some label => {label} | none => ∅) ∪
      (match handler with | some (_, body) => getCodeLabels body | none => ∅)
  | .force _ label _ => {label}
  | .seq first second => getCodeLabels first ∪ getCodeLabels second
  | .ifThenElse _ first second => getCodeLabels first ∪ getCodeLabels second
  | .assign _ op _ _ => ClosLang.assignGetCodeLabel op
  | _ => ∅

/-- Adding ticks cannot introduce a code label. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "get_code_labels_mk_ticks"]
theorem getCodeLabels_mkTicks (n : Nat) (program : DataLang.Prog) :
    getCodeLabels (DataLang.mkTicks n program) ⊆ getCodeLabels program := by
  induction n with
  | zero => simp [DataLang.mkTicks]
  | succ n ih => simpa [DataLang.mkTicks, getCodeLabels] using ih

end Flapjack.Compiler.Backend.DataSem
