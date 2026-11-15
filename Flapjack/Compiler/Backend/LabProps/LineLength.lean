module

public import Flapjack.Compiler.Backend.LabSem.Navigation
public import Flapjack.Compiler.Backend.LabToTarget.RemoveLabels

@[expose] public section

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

/-- Exact HOL `LENGTH_line_bytes` (`labPropsScript.sml:265`): a non-label line
    has as many bytes as its physical length. The premise is HOL's
    `~is_Label x2`, which is the Boolean equation `is_Label x2 = F`; `is_Label`
    is the reviewed `isLabelHOL` classifier. -/
@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "LENGTH_line_bytes"
  (words_as_type_indexed_bitvec)]
theorem length_line_bytes {width : Nat} [NeZero width]
    (x2 : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :
    LabSem.isLabelHOL x2 = false → (LabToTarget.lineBytes x2).length = lineLength x2 := by
  intro h
  cases x2 with
  | label k1 k2 l => simp [LabSem.isLabelHOL] at h
  | asm b bytes l => simp [LabToTarget.lineBytes, lineLength]
  | labAsm a w bytes l => simp [LabToTarget.lineBytes, lineLength]

end Flapjack.Compiler.Backend.LabProps
