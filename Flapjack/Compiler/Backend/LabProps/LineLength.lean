import Flapjack.Compiler.Backend.LabSem.Navigation

namespace Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-- Original physical line length. Labels contribute zero or one according to
whether their annotation is zero; instructions contribute their byte-list length.
The instruction length annotation is intentionally not read by this operation. -/
@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml"
  "line_length_def" (words_as_type_indexed_bitvec)]
def lineLength {width : Nat} [NeZero width]
    (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) : Nat :=
  match line with
  | .label _ _ length => if length = 0 then 0 else 1
  | .asm _ bytes _ => bytes.length
  | .labAsm _ _ bytes _ => bytes.length

end Flapjack.Compiler.Backend.LabProps
