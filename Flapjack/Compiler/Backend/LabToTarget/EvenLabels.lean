import Flapjack.Compiler.Backend.LabToTarget.LineLength
import Flapjack.Compiler.Backend.LabSem.Classifier
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Original label parity at the position before consuming each line. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def linesEvenLabels {width : Nat} [NeZero width] (pos : Nat) : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) → Prop
  | [] => True
  | line::rest => (isLabelHOL line = true → pos % 2 = 0) ∧
      linesEvenLabels (pos + lineLen line) rest

/-- Original weak predicate, including its unconstrained empty-section case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def evenLabels {width : Nat} [NeZero width] (pos : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : Prop :=
  match code with
  | [] => True
  | ⟨_,[]⟩::rest => evenLabels pos rest
  | ⟨k,line::lines⟩::rest => (isLabelHOL line = true → pos % 2 = 0) ∧
      evenLabels (pos + lineLen line) (⟨k,lines⟩::rest)
termination_by code.length + (code.map (fun sec => sec.lines.length)).sum
decreasing_by all_goals simp_wf

/-- Original strong predicate also checks parity at every section end. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def evenLabelsStrong {width : Nat} [NeZero width] (pos : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : Prop :=
  match code with
  | [] => True
  | ⟨_,[]⟩::rest => pos % 2 = 0 ∧ evenLabelsStrong pos rest
  | ⟨k,line::lines⟩::rest => (isLabelHOL line = true → pos % 2 = 0) ∧
      evenLabelsStrong (pos + lineLen line) (⟨k,lines⟩::rest)
termination_by code.length + (code.map (fun sec => sec.lines.length)).sum
decreasing_by all_goals simp_wf

/-- Full original section decomposition; annotation lengths advance position.
The empty-code conjunct has an independent HOL word dimension, retained here
as `emptyWidth` rather than specializing it to the section dimension. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evenLabels_alt {emptyWidth : Nat} {width : Nat} [NeZero emptyWidth] [NeZero width] (pos : Nat) (k : Nat)
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (rest : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (evenLabels (width := emptyWidth) pos [] ↔ True) ∧
    (evenLabels pos (⟨k,lines⟩::rest) ↔ linesEvenLabels pos lines ∧
      evenLabels (pos + (lines.map lineLen).sum) rest) := by
  constructor
  · simp [evenLabels]
  · induction lines generalizing pos with
    | nil => simp [evenLabels,linesEvenLabels]
    | cons line lines ih =>
      rw [evenLabels,linesEvenLabels,ih]
      simp [Nat.add_assoc,and_assoc]

/-- Full original arbitrary-position append equivalence. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem linesEvenLabels_append {width : Nat} [NeZero width]
    (left right : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (pos : Nat) :
    linesEvenLabels pos (left ++ right) ↔ linesEvenLabels pos left ∧
      linesEvenLabels (pos + (left.map lineLen).sum) right := by
  induction left generalizing pos with
  | nil => simp [linesEvenLabels]
  | cons line left ih =>
    simp [linesEvenLabels,ih,Nat.add_assoc,and_assoc]
end Flapjack.Compiler.Backend.LabToTarget
