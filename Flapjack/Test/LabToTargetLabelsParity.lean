import Flapjack.Compiler.Backend.LabToTarget.Labels
import Flapjack.Compiler.Encoders.Asm
import Flapjack.Basis.Pure.MlString

/-!
# Original-HOL parity for Lab-to-target label computation

Kernel replays matching the six rows of `scripts/hol-probes/lab_to_target_labels_probe.out`.
-/

namespace Flapjack.Test.LabToTargetLabelsParity

open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm

private abbrev L := Line (AsmOrCbw (HolAsm 8) HolMemop (HolAddr 8))
  (AsmWithLab HolCmp (HolRegImm 8) Flapjack.Basis.Pure.MlString.MlString) (BitVec 8)

private def skipLine : L := .asm (.asmi (.inst .skip)) [] 4

example : sectionLabels 0 ([] : List L) [] = (0, []) := by decide

example :
    sectionLabels 5 ([.label 1 2 3, skipLine, .label 1 0 2] : List L) [] = (14, [(2, 8)]) := by
  decide +kernel

example : sectionLabels 0 ([.label 1 0 7] : List L) [] = (7, []) := by decide

example : computeLabelsAlt 0 ([] : List (Section L)) .ln = .ln := by rfl

example :
    lookupAny 2 (lookupAny 7
      (computeLabelsAlt 0 ([⟨7, [.label 7 2 3, skipLine]⟩] : List (Section L)) .ln) .ln) 0 = 3 := by
  decide +kernel

example :
    lookupAny 0 (lookupAny 7
      (computeLabelsAlt 0 ([⟨7, [.label 7 2 3]⟩] : List (Section L)) .ln) .ln) 0 = 0 := by
  decide +kernel

def runChecks : IO Bool := do
  IO.println "PASS exact lab_to_target labels match six original HOL rows"
  pure true

end Flapjack.Test.LabToTargetLabelsParity
