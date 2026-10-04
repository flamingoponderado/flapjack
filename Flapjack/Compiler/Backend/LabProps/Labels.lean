import Flapjack.Compiler.Backend.LabSem.State

namespace Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def secLabelOk {width : Nat} [NeZero width] (sectionId : Nat) (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) : Prop :=
  match line with
  | .label s label _ => s = sectionId ∧ label ≠ 0
  | _ => True

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def secLabelsOk {width : Nat} [NeZero width] (sec : Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) : Prop :=
  ∀ line ∈ sec.lines, secLabelOk sec.sectionId line

end Flapjack.Compiler.Backend.LabProps
