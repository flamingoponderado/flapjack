import Flapjack.Compiler.Backend.LabToTarget.Positions

namespace Flapjack.Test.LabToTargetPositionsParity
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm
private abbrev Ml := Flapjack.Basis.Pure.MlString.MlString
private abbrev mkStr := Flapjack.Basis.Pure.MlString.ofString

private def labs : Spt (Spt Nat) := sptInsert 3 (sptInsert 5 0 .ln) .ln

example : findPos (Lab.lab 3 5) labs = 0 := by cbv
example : findPos (Lab.lab 3 6) labs = 0 := by cbv
example : findPos (Lab.lab 1 2) (.ln : Spt (Spt Nat)) = 0 := by cbv
example : getLabel (AsmWithLab.jump (Lab.lab 3 5) : AsmWithLab HolCmp (HolRegImm 8) Ml) = Lab.lab 3 5 := by cbv
example : getLabel (AsmWithLab.call (Lab.lab 1 2) : AsmWithLab HolCmp (HolRegImm 8) Ml) = Lab.lab 1 2 := by cbv
example : getLabel (AsmWithLab.install : AsmWithLab HolCmp (HolRegImm 8) Ml) = Lab.lab 0 0 := by cbv
example : getFfiIndex [HolFfiName.extCall (mkStr "a"), HolFfiName.extCall (mkStr "b")]
    (HolFfiName.extCall (mkStr "b")) = 1 := by cbv
example : getFfiIndex [HolFfiName.extCall (mkStr "a")]
    (HolFfiName.extCall (mkStr "z")) = 0 := by cbv
example : getJumpOffset (AsmWithLab.jump (Lab.lab 3 5) : AsmWithLab HolCmp (HolRegImm 8) Ml)
    ([] : List HolFfiName) labs 7 = 249#8 := by cbv
example : getJumpOffset (AsmWithLab.install : AsmWithLab HolCmp (HolRegImm 8) Ml)
    ([] : List HolFfiName) labs 7 = 217#8 := by cbv
example : getJumpOffset (AsmWithLab.halt : AsmWithLab HolCmp (HolRegImm 8) Ml)
    ([] : List HolFfiName) labs 7 = 233#8 := by cbv
example : getJumpOffset (AsmWithLab.callFFI (mkStr "b") : AsmWithLab HolCmp (HolRegImm 8) Ml)
    [HolFfiName.extCall (mkStr "a"), HolFfiName.extCall (mkStr "b")] labs 7 = 185#8 := by cbv

def runChecks : IO Bool := do
  IO.println "PASS exact lab_to_target positions match twelve original HOL rows"
  pure true
end Flapjack.Test.LabToTargetPositionsParity
