import Flapjack.Compiler.Backend.LabToTarget.SectionNavigation

namespace Flapjack.Test.LabToTargetSectionLookupParity
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabProps
private def lines : List (LabLineHOL 8) :=
  [.asm (.cbw 1 2) [] 99, .label 1 5 42, .labAsm .halt 0 [] 88, .label 1 7 43]
private def one : LabProgHOL 8 := [⟨1, lines⟩]
private def code : LabProgHOL 8 :=
  [⟨9, [.asm (.cbw 3 4) [] 100, .label 9 8 44]⟩, ⟨1, lines⟩, ⟨2, []⟩]

-- Each row in the original HOL capture is replayed through the actual native
-- lookup, rewritten by the section theorem; section-local results are not an oracle.
private theorem one_valid : ∀ sec ∈ one, secLabelsOk sec := by
  simp [one, lines, secLabelsOk, secLabelOk]
private theorem code_valid : ∀ sec ∈ code, secLabelsOk sec := by
  simp [code, lines, secLabelsOk, secLabelOk]

example : locToPc 1 0 one = some 0 := by
  rw [locToPc_sections _ _ _ one_valid]
  simp [one, lines, secLocToPc]
example : locToPc 1 5 one = some 1 := by
  rw [locToPc_sections _ _ _ one_valid]
  simp [one, lines, secLocToPc, isLabelHOL]
example : locToPc 1 7 one = some 2 := by
  rw [locToPc_sections _ _ _ one_valid]
  simp [one, lines, secLocToPc, isLabelHOL]
example : locToPc 1 99 one = none := by
  rw [locToPc_sections _ _ _ one_valid]
  simp [one, lines, secLocToPc, isLabelHOL, locToPc]
example : locToPc 1 0 code = some 1 := by
  rw [locToPc_sections _ _ _ code_valid]
  simp [code, lines, lenNoLab, isLabelHOL, locToPc]
example : locToPc 1 5 code = some 2 := by
  rw [locToPc_sections _ _ _ code_valid]
  simp [code, lines, lenNoLab, isLabelHOL, locToPc]
example : locToPc 2 0 code = some 3 := by
  rw [locToPc_sections _ _ _ code_valid]
  simp [code, lines, lenNoLab, isLabelHOL, locToPc]
example : locToPc 2 5 code = none := by
  rw [locToPc_sections _ _ _ code_valid]
  simp [code, lines, lenNoLab, isLabelHOL, locToPc]

def runChecks : IO Unit :=
  IO.println "PASS original section-wise label lookup (8 kernel replays via loc_to_pc_thm)"
end Flapjack.Test.LabToTargetSectionLookupParity
