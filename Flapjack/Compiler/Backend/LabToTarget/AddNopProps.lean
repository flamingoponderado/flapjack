import Flapjack.Compiler.Backend.LabToTarget.Padding
import Flapjack.Compiler.Backend.LabToTarget.LineLength
import Flapjack.Compiler.Backend.LabProps.LineLength
import Flapjack.Compiler.Backend.LabSem.Classifier
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem lineLength_addNop_nonlabel {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    ¬(∀ line ∈ ls, isLabelHOL line = true) →
    ((addNop nop ls).map lineLength).sum = (ls.map lineLength).sum + nop.length := by
  induction ls with
  | nil => simp
  | cons x xs ih =>
    intro hn
    cases x with
    | label k1 k2 n =>
      have ht : ¬(∀ line ∈ xs, isLabelHOL line = true) := by
        simpa [isLabelHOL] using hn
      have hh := ih ht
      simp only [addNop,List.map_cons,List.sum_cons,lineLength]
      omega
    | asm a bs n => simp [addNop,lineLength,List.length_append]; omega
    | labAsm a w bs n => simp [addNop,lineLength,List.length_append]; omega

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem lineLength_addNop_labels {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    (∀ line ∈ ls, isLabelHOL line = true) →
    ((addNop nop ls).map lineLength).sum = (ls.map lineLength).sum := by
  induction ls with
  | nil => simp [addNop]
  | cons x xs ih => cases x <;> simp_all [addNop,lineLength,isLabelHOL]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem lineLen_addNop_nonlabel {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    ¬(∀ line ∈ ls, isLabelHOL line = true) →
    ((addNop nop ls).map lineLen).sum = (ls.map lineLen).sum + 1 := by
  induction ls with
  | nil => simp
  | cons x xs ih =>
    intro hn
    cases x with
    | label k1 k2 n =>
      have ht : ¬(∀ line ∈ xs, isLabelHOL line = true) := by
        simpa [isLabelHOL] using hn
      have hh := ih ht
      simp only [addNop,List.map_cons,List.sum_cons,lineLen]
      omega
    | asm a bs n => simp [addNop,lineLen]; omega
    | labAsm a w bs n => simp [addNop,lineLen]; omega

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem lineLen_addNop_labels {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    (∀ line ∈ ls, isLabelHOL line = true) →
    ((addNop nop ls).map lineLen).sum = (ls.map lineLen).sum := by
  induction ls with
  | nil => simp [addNop]
  | cons x xs ih => cases x <;> simp_all [addNop,lineLen,isLabelHOL]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem addNop_append {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (l1 l2 : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    addNop nop (l1 ++ l2) = if l1.all isLabelHOL then l1 ++ addNop nop l2 else addNop nop l1 ++ l2 := by
  induction l1 with
  | nil => rfl
  | cons x xs ih =>
    cases x <;> simp_all [addNop,isLabelHOL]
    split <;> rfl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem existsNotLabel_addNop {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    (∃ line ∈ addNop nop acc, isLabelHOL line ≠ true) ↔
    (∃ line ∈ acc, isLabelHOL line ≠ true) := by
  induction acc with
  | nil => simp [addNop]
  | cons x xs ih => cases x <;> simp_all [addNop,isLabelHOL]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem everyIsLabel_addNop {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    (∀ line ∈ addNop nop acc, isLabelHOL line = true) ↔
    (∀ line ∈ acc, isLabelHOL line = true) := by
  induction acc with
  | nil => simp [addNop]
  | cons x xs ih => cases x <;> simp_all [addNop,isLabelHOL]
end Flapjack.Compiler.Backend.LabToTarget
