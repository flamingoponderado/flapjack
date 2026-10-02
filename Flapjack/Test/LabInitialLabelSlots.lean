import Flapjack.RiscV.Lab

namespace Flapjack.Test.LabInitialLabelSlots
open Flapjack Flapjack.RiscV

/-! Production regression for native sections, which have no synthetic entry
labels. HOL lab_to_targetScript enc_line_def initializes every Label with the
encoded Skip length, including labels among the first two lines. -/

example (sectionId first second third : Nat) :
    (labInitialStoredProgram (width := 64)
      [{ name := sectionId, lines := [.label sectionId first 0,
          .label sectionId second 37, .label sectionId third 0] }]).map
        (fun s => s.lines.map labStoredLineLength) = [[4, 4, 4]] := by
  rfl

example (sectionId label : Nat) :
    (labInitialStoredProgram (width := 64)
      [{ name := sectionId, lines := [.asm .tick [] 0, .label sectionId label 0] }]).map
        (fun s => s.lines.map labStoredLineLength) = [[0, 4]] := by
  rfl

example (sectionId label : Nat) :
    (labInitialStoredProgram (width := 64)
      [{ name := sectionId, lines := [.label sectionId label 0] },
       { name := sectionId + 1, lines := [.label (sectionId + 1) 0 0] }]).map
        (fun s => s.lines.map labStoredLineLength) = [[4], [4]] := by
  rfl

end Flapjack.Test.LabInitialLabelSlots
