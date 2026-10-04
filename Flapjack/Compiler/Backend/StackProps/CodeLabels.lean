import Flapjack.Compiler.Backend.StackLang.Prog
import Mathlib.Data.Set.Basic

namespace Flapjack.Compiler.Backend.StackProps
open StackLang

/-- Literal handler-label extraction. A nonreturning Call contributes no
handler labels, even when its handler field is populated. Returning Calls
recurse into both bodies and include a handler label only for the named owner. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def stackGetHandlerLabels {width : Nat} [NeZero width] (owner : Nat) :
    HolProg width → Set (Nat × Nat)
  | .call none _ _ => ∅
  | .call (some (body, _, _, _)) _ handler =>
      stackGetHandlerLabels owner body ∪
        match handler with
        | some (body, label, entry) =>
            (if label = owner then {(label, entry)} else ∅) ∪
              stackGetHandlerLabels owner body
        | none => ∅
  | .seq first second => stackGetHandlerLabels owner first ∪ stackGetHandlerLabels owner second
  | .ite _ _ _ first second =>
      stackGetHandlerLabels owner first ∪ stackGetHandlerLabels owner second
  | .loop body => stackGetHandlerLabels owner body
  | _ => ∅

/-- Literal referenced-code label extraction. Call continuations are traversed
independently: a populated handler contributes code labels even when the return
field is NONE. RawCall uses entry one; JumpLower and direct Call use entry zero. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def getCodeLabels {width : Nat} [NeZero width] : HolProg width → Set (Nat × Nat)
  | .call returnBody target handler =>
      (match target with
        | .inl label => {(label, 0)}
        | .inr _ => ∅) ∪
      (match returnBody with
        | some (body, _, _, _) => getCodeLabels body
        | none => ∅) ∪
      (match handler with
        | some (body, _, _) => getCodeLabels body
        | none => ∅)
  | .seq first second => getCodeLabels first ∪ getCodeLabels second
  | .ite _ _ _ first second => getCodeLabels first ∪ getCodeLabels second
  | .loop body => getCodeLabels body
  | .jumpLower _ _ target => {(target, 0)}
  | .rawCall target => {(target, 1)}
  | .locValue _ label entry => {(label, entry)}
  | .storeConsts _ _ (some label) => {(label, 0)}
  | _ => ∅

end Flapjack.Compiler.Backend.StackProps
