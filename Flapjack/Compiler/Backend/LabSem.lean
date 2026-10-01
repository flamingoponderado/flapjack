import Flapjack.Compiler.Backend.LabLang
import Flapjack.HolRef

/-!
# Generic LabLang classification utility

The generic classifier is retained for compatibility callers. Its arbitrary
ASM and word payload types are broader than HOL's actual LabLang carrier,
even though the classification ignores those payloads. It is therefore not
a tagged HOL port. The faithful native classifier lives in `LabSem.Classifier`.
-/

namespace Flapjack.Compiler.Backend.LabSem

open Flapjack.Compiler.Backend.LabLang

/-- Flapjack-specific generic classifier: true exactly on label constructors.
It generalizes the payload carriers beyond HOL and has no HOL declaration at
this arbitrary-type signature. The native restriction is checked separately. -/
def isLabel {AsmOrCbw AsmWithLab Word : Type}
    (line : Line AsmOrCbw AsmWithLab Word) : Bool :=
  match line with
  | .label _ _ _ => true
  | _ => false

end Flapjack.Compiler.Backend.LabSem
