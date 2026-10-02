import Flapjack.Compiler.Backend.LabToTarget.PositionValues

namespace Flapjack.Test.LabToTargetPositionValuesParity
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabProps
private def lines : List (LabLineHOL 8) :=
  [.label 1 5 0, .label 1 6 42, .asm (.cbw 1 2) [1,2] 99,
   .label 1 7 100, .labAsm .halt 0 [3,4,5] 88, .label 1 8 0]
private def code : LabProgHOL 8 :=
  [⟨9, []⟩, ⟨1, lines⟩, ⟨2, [.label 2 4 2, .asm (.cbw 3 4) [6] 100]⟩, ⟨3, []⟩]
example : lineLength (.label 1 5 0 : LabLineHOL 1) = 0 := by decide +kernel
example : lineLength (.label 1 5 99 : LabLineHOL 80) = 1 := by decide +kernel
example : lineLength (.asm (.cbw 1 2) [1,2] 99 : LabLineHOL 8) = 2 := by decide +kernel
example : lineLength (.labAsm .halt 0 [3,4,5] 88 : LabLineHOL 8) = 3 := by decide +kernel
example : secPosVal 0 10 lines = some 11 := by decide +kernel
example : secPosVal 1 10 lines = some 14 := by decide +kernel
example : secPosVal 2 10 lines = none := by decide +kernel
example : secPosVal 99 10 lines = none := by decide +kernel
example : secPosVal 0 10 ([.label 1 5 99, .label 1 6 0] : List (LabLineHOL 80)) = none := by decide +kernel
example : posVal 0 10 code = 11 := by decide +kernel
example : posVal 1 10 code = 14 := by decide +kernel
example : posVal 2 10 code = 18 := by decide +kernel
example : posVal 3 10 code = 19 := by decide +kernel
example : posVal 99 10 code = 19 := by decide +kernel
example : posVal 99 10 ([] : LabProgHOL 80) = 10 := by decide +kernel
-- Full arbitrary-width applications retain all native instructions and annotation values.
example {width : Nat} [NeZero width] (xs : List (LabLineHOL width)) (n : Nat) :
    secPosVal (lenNoLab xs) n xs = none := secPosVal_tooBig _ _ _ (Nat.le_refl _)
example {width : Nat} [NeZero width] (xs : List (LabLineHOL width))
    (n pos : Nat) (h : ∀ x ∈ xs, isLabelHOL x = true) :
    secPosVal n pos xs = none := everyIsLabel_secPosVal _ _ _ h
example {width : Nat} [NeZero width] (xs : LabProgHOL width) (n : Nat) :
    posVal (xs.map (fun sec => lenNoLab sec.lines)).sum n xs =
    n + (xs.map (fun sec => (sec.lines.map lineLength).sum)).sum := posVal_acc xs n

example : posVal 1 10 ([] : LabProgHOL 1) = 10 ∧
    posVal 1 10 (⟨1, lines⟩ :: []) =
      match secPosVal 1 10 lines with
      | none => posVal (1 - lenNoLab lines) (10 + (lines.map lineLength).sum) ([] : LabProgHOL 8)
      | some x => x := posVal_sections (emptyWidth := 1) 1 10 1 lines []
example : posVal 1 10 ([] : LabProgHOL 80) = 10 ∧
    posVal 1 10 (⟨1, lines⟩ :: []) =
      match secPosVal 1 10 lines with
      | none => posVal (1 - lenNoLab lines) (10 + (lines.map lineLength).sum) ([] : LabProgHOL 8)
      | some x => x := posVal_sections (emptyWidth := 80) 1 10 1 lines []

def runChecks : IO Bool := do
  IO.println "PASS original native position values (15 observations, 5 full generic/mixed-width applications)"
  return true
end Flapjack.Test.LabToTargetPositionValuesParity
