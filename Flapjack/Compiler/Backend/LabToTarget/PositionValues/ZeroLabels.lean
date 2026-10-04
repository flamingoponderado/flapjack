import Flapjack.Compiler.Backend.LabToTarget.PositionAppend
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabProps
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Complete original zero-instruction position law. Empty/all-label lists
are excluded only by the original NOT EVERY classifier guard. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem secPosVal_zero {width : Nat} [NeZero width] (pos : Nat)
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    ¬(∀ line ∈ lines, isLabelHOL line = true) ∧
      (∀ line ∈ lines, labelZero line) → secPosVal 0 pos lines = some pos := by
  induction lines generalizing pos with
  | nil => simp
  | cons line lines ih =>
    rintro ⟨hnot,hzero⟩
    have hz := hzero line (by simp)
    have ht : ∀ line ∈ lines,labelZero line := fun l hm => hzero l (by simp [hm])
    cases line with
    | label k1 k2 len =>
      have hn : len = 0 := hz
      subst len
      have hl : ¬(∀ line ∈ lines,isLabelHOL line = true) := by
        simpa [isLabelHOL] using hnot
      simpa [secPosVal,isLabelHOL,lineLength] using ih pos ⟨hl,ht⟩
    | asm _ _ _ | labAsm _ _ _ _ => simp [secPosVal,isLabelHOL]
end Flapjack.Compiler.Backend.LabToTarget
