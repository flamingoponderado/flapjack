import Flapjack.Compiler.Backend.LabSem.Classifier
import Flapjack.Compiler.Backend.LabProps

namespace Flapjack.Compiler.Backend.LabProps

open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-- Native port of HOL section-end predicate over the actual LabLang payloads.
The reverse-head cases implement nonempty plus classification of LAST, whose
unspecified empty-list value is irrelevant behind the nonempty conjunct.
Encoded bytes retain the original fixed8 carrier and names the native MlString.
Only the positive polymorphic HOL word dimension uses the reviewed translation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def secEndsWithLabelNative {width : Nat} [NeZero width]
    (sec : Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) : Prop :=
  match sec.lines.reverse with
  | [] => False
  | line :: _ => LabSem.isLabelHOL line = true

/-- Flapjack-specific compatibility infrastructure without a HOL original:
restriction of the broad local utility to native payloads is unconditional. -/
theorem secEndsWithLabelNative_iff_generic {width : Nat} [NeZero width]
    (sec : LabSem.LabSectionHOL width) :
    secEndsWithLabelNative sec ↔ secEndsWithLabelHOL sec := by
  unfold secEndsWithLabelNative secEndsWithLabelHOL
  cases sec.lines.reverse with
  | nil => rfl
  | cons line rest => simp only [LabSem.isLabelHOL_eq_generic]

end Flapjack.Compiler.Backend.LabProps
