import Flapjack.Compiler.Backend.LabToTarget.PositionAppend

namespace Flapjack.Test.LabToTargetPositionAppendParity
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabSem
private def codePrefix : LabProgHOL 8 :=
  [⟨1, [.label 1 1 7, .asm (.cbw 1 2) [1,2] 99, .label 1 2 0,
    .labAsm .halt 0 [3] 88, .label 1 3 9]⟩]
private def suffix : LabProgHOL 8 :=
  [⟨2, [.label 2 4 0, .asm (.cbw 3 4) [4,5,6] 77, .label 2 5 0]⟩, ⟨3, []⟩]
private def labels : LabProgHOL 8 := [⟨9, [.label 9 1 2, .label 9 2 99]⟩]
example : labelZero (.label 1 2 0 : LabLineHOL 1) := by simp [labelZero]
example : ¬ labelZero (.label 1 2 9 : LabLineHOL 80) := by simp [labelZero]
example : labelZero (.asm (.cbw 1 2) [] 99 : LabLineHOL 8) := by simp [labelZero]
example : labelZero (.labAsm .halt 0 [] 88 : LabLineHOL 8) := by simp [labelZero]
private theorem suffix_valid : ∀ sec ∈ suffix, secLabelZero sec := by
  simp [suffix, secLabelZero, labelZero]
example : ¬ (∀ sec ∈ codePrefix, secLabelZero sec) := by
  simp [codePrefix, secLabelZero, labelZero]
example : posVal 0 10 suffix = 10 := by decide +kernel
example : posVal 1 10 (codePrefix ++ suffix) = 13 := by decide +kernel
example : posVal 2 10 (codePrefix ++ suffix) = 15 := by decide +kernel
example : posVal 2 10 codePrefix = 15 := by decide +kernel
example : posVal 0 15 suffix = 15 := by decide +kernel
example : posVal 3 10 (codePrefix ++ suffix) = 18 := by decide +kernel
example : posVal 99 10 (codePrefix ++ suffix) = 18 := by decide +kernel
example : posVal 0 10 (([] : LabProgHOL 8) ++ suffix) = 10 := by decide +kernel
example : posVal 99 10 (codePrefix ++ []) = 15 := by decide +kernel
example : posVal 0 10 (labels ++ suffix) = 12 := by decide +kernel
example : posVal 1 10 (labels ++ suffix) = 15 := by decide +kernel
-- These applications prove concrete output through the full append theorem.
example : posVal 2 10 (codePrefix ++ suffix) = 15 := by
  rw [posVal_append codePrefix 2 10 suffix suffix_valid]
  decide +kernel
example : posVal 3 10 (codePrefix ++ suffix) = 18 := by
  rw [posVal_append codePrefix 3 10 suffix suffix_valid]
  decide +kernel
-- Boundary and offset consequences retain arbitrary native instruction payloads.
example {width : Nat} [NeZero width] (c1 c2 : LabProgHOL width) (pos : Nat)
    (h : ∀ sec ∈ c2, secLabelZero sec) :
    posVal (c1.map (fun sec => lenNoLab sec.lines)).sum pos (c1 ++ c2) =
    posVal (c1.map (fun sec => lenNoLab sec.lines)).sum pos c1 := by
  rw [posVal_append c1 _ pos c2 h]
  simp
example {width : Nat} [NeZero width] (c1 c2 : LabProgHOL width) (pos n : Nat)
    (h : ∀ sec ∈ c2, secLabelZero sec) :
    posVal ((c1.map (fun sec => lenNoLab sec.lines)).sum + n + 1) pos (c1 ++ c2) =
    posVal (n + 1) (pos + (c1.map (fun sec => (sec.lines.map lineLength).sum)).sum) c2 := by
  rw [posVal_append c1 _ pos c2 h]
  have hn : ¬ (c1.map (fun sec => lenNoLab sec.lines)).sum + n + 1 ≤
      (c1.map (fun sec => lenNoLab sec.lines)).sum := by omega
  simp only [if_neg hn]
  congr 1
  simp [Nat.add_assoc]
example {width : Nat} [NeZero width] (xs : LabProgHOL width) (pos : Nat)
    (h : ∀ sec ∈ xs, secLabelZero sec) :
    posVal 0 pos xs = pos := secLabelZero_posVal_zero xs pos h

def runChecks : IO Bool := do
  IO.println "PASS original native position append (17 observations, 5 full theorem applications)"
  return true
end Flapjack.Test.LabToTargetPositionAppendParity
