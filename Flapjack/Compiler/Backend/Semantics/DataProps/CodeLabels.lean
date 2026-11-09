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

end Flapjack.Compiler.Backend.DataSem
