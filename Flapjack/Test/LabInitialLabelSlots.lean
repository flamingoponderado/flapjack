import Flapjack.RiscV.InitializedRuntime

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

/-! Relocation budget regression: a changing stored length must not be emitted
when no subsequent sweep can confirm convergence. Empty programs converge in
one sweep; an undersized plain instruction needs a second sweep. -/
example (context : WordFfiContext) (haltPc : Nat)
    (program : LabProgram (Word 64)) :
    initializedRuntimeEncodeStable 0 context haltPc program = none := by
  rfl

private def relocationContext : WordFfiContext := { services := [] }
private def undersizedProgram : LabProgram (Word 64) :=
  [{ name := 3, lines := [.asm (.word (.const 0 0)) [] 0] }]

#guard (initializedRuntimeEncodeStable 0 relocationContext 0
  ([] : LabProgram (Word 64))).isNone
#guard (initializedRuntimeEncodeStable 1 relocationContext 0
  ([] : LabProgram (Word 64))).isSome
#guard (initializedRuntimeEncodeStable 1 relocationContext 0 undersizedProgram).isNone
#guard (initializedRuntimeEncodeStable 2 relocationContext 0 undersizedProgram).isSome
#guard (initializedRuntimeEncodeStable 2 relocationContext 0 undersizedProgram).map
  labStoredLineLengths == some [4]
#guard (compileLabProgramLinkedWithNativeInitialization relocationContext
  ([] : LabProgram (Word 64))).isSome

end Flapjack.Test.LabInitialLabelSlots
