import Flapjack.Compiler.Backend.LabToTarget.Encoding
import Flapjack.Compiler.Backend.LabSem.Navigation

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem Flapjack.Basis.Pure.MlString

/-- Flapjack induction infrastructure: navigation ignores encoding bytes,
recorded lengths and resolved words, even when section ownership is invalid.
The arbitrary skip length here is not an independently named HOL theorem. -/
private theorem locToPc_mapEncSec {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (skipLen sectionId labelId : Nat)
    (code : List (Section (LabLineHOL width))) :
    locToPc sectionId labelId (code.map (encSec enc skipLen)) =
      locToPc sectionId labelId code := by
  induction code with
  | nil => simp [locToPc]
  | cons sec rest ih =>
    rcases sec with ⟨sid, lines⟩
    simp only [List.map_cons]
    induction lines with
    | nil => simp [encSec, locToPc, ih]
    | cons line lines hlines =>
      cases line <;>
        simp [encSec, encLine, locToPc, isLabelHOL] at hlines ⊢ <;>
        split <;> simp_all

/-- Full original unconditional navigation equality. The encoder is arbitrary;
there is no successful encoding or section-label validity premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem locToPc_encSecList {width : Nat} [NeZero width]
    (sectionId labelId : Nat) (code : List (Section
      (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
        (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (enc : HolAsm width → List (BitVec 8)) :
    locToPc sectionId labelId (encSecList enc code) = locToPc sectionId labelId code := by
  exact locToPc_mapEncSec enc (enc (.inst .skip)).length sectionId labelId code

end Flapjack.Compiler.Backend.LabToTarget
