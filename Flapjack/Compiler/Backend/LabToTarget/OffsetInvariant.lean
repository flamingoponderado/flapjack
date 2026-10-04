import Flapjack.Compiler.Backend.LabToTarget.Positions
import Flapjack.Compiler.Backend.LabToTarget.SectionLength
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Original proof-side stored jump-offset invariant, observing every labelled
opcode at the current annotation position and imposing nothing on other lines. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def lineOffsetOk {width : Nat} [NeZero width] (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width) → Prop
  | .labAsm a w _ _ => w = getJumpOffset a ffis labs pos
  | _ => True

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def linesOffsetOk {width : Nat} [NeZero width] (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) → Prop
  | [] => True
  | l :: ls => lineOffsetOk labs ffis pos l ∧ linesOffsetOk labs ffis (pos + lineLen l) ls

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem linesOffsetOk_append {width : Nat} [NeZero width] (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (l1 l2 : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    linesOffsetOk labs ffis pos (l1 ++ l2) ↔
    linesOffsetOk labs ffis pos l1 ∧ linesOffsetOk labs ffis (pos + (l1.map lineLen).sum) l2 := by
  induction l1 generalizing pos with
  | nil => simp [linesOffsetOk]
  | cons l ls ih => simp [linesOffsetOk,ih,Nat.add_assoc,and_assoc]

/-- Original section offset traversal advances through recorded annotations,
including empty sections; section identifiers and physical bytes are unobserved. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def offsetOk {width : Nat} [NeZero width] (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) → Prop
  | [] => True
  | sec :: rest => linesOffsetOk labs ffis pos sec.lines ∧
      offsetOk labs ffis (pos + (sec.lines.map lineLen).sum) rest
end Flapjack.Compiler.Backend.LabToTarget
