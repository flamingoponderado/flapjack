import Flapjack.Compiler.Backend.StackLang
import Flapjack.Compiler.Backend.StackLang.Prog
import Flapjack.HolRef

namespace Flapjack.StackSemLabels

open Flapjack.Compiler.Backend.StackLang

/-- Untagged candidate for HOL get_labels_def (stackSemScript667-679),
represented by its membership predicate. Exact-tag acceptance remains open:
the words qualifier checker cannot yet resolve the HolProg alias. In the Call
NONE clause HOL ignores the exception handler as well as returning no labels.
This proof-side extractor is not an executed evaluator or a production route. -/
def getLabels {width : Nat} [NeZero width] : HolProg width → (Nat × Nat) → Prop
  | .seq p q, label => getLabels p label ∨ getLabels q label
  | .ite _ _ _ p q, label => getLabels p label ∨ getLabels q label
  | .loop p, label => getLabels p label
  | .call none _ _, _ => False
  | .call (some (p, _, l1, l2)) _ handler, label =>
      (label = (l1, l2) ∨ getLabels p label) ∨
        match handler with
        | none => False
        | some (q, h1, h2) => label = (h1, h2) ∨ getLabels q label
  | _, _ => False

end Flapjack.StackSemLabels
