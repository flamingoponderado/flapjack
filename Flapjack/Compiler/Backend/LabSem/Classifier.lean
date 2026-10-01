import Flapjack.Compiler.Backend.LabSem.State
import Flapjack.Compiler.Backend.LabSem

namespace Flapjack.Compiler.Backend.LabSem

open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-- The literal HOL classifier over the actual native LabLang carrier, with
one shared positive word width and the exact ASM/mlstring payloads. -/
@[hol "cakeml/compiler/backend/semantics/labSemScript.sml" "is_Label_def"
  (words_as_type_indexed_bitvec)]
def isLabelHOL {width : Nat} [NeZero width]
    (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) : Bool :=
  match line with
  | .label _ _ _ => true
  | _ => false

/-- Flapjack-specific compatibility fact, with no HOL original: restricting
the broad utility to native payloads agrees unconditionally with the reviewed
classifier. This preserves its existing clients without treating the broad
signature as a HOL port. -/
theorem isLabelHOL_eq_generic {width : Nat} [NeZero width] (line : LabLineHOL width) :
    isLabelHOL line = isLabel line := by
  cases line <;> rfl

end Flapjack.Compiler.Backend.LabSem
