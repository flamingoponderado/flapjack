import Flapjack.Compiler.Backend.LabFilter.Map
import Flapjack.Compiler.Backend.LabProps.SectionEnd

namespace Flapjack.Compiler.Backend.LabFilter.Proofs
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabProps

/-- Full original EVERY section-end preservation. The native nonempty reverse
head implements the guarded LAST predicate, so the proof never fixes LAST on
an empty list. Labels are retained by the actual skip filter. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem secEndsWithLabelFilterSkip {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
      (BitVec width)))) :
    (∀ sectionData ∈ code, secEndsWithLabelNative sectionData) →
    ∀ sectionData ∈ filterSkip code, secEndsWithLabelNative sectionData := by
  intro hsource sectionData hmem
  rw [filterSkipMap] at hmem
  obtain ⟨sectionData, hsection, rfl⟩ := List.mem_map.mp hmem
  rcases sectionData with ⟨sid, lines⟩
  have hend := hsource ⟨sid, lines⟩ hsection
  change (match lines.reverse with
    | [] => False
    | line :: _ => isLabelHOL line = true) at hend
  change (match (lines.filter notSkip).reverse with
    | [] => False
    | line :: _ => isLabelHOL line = true)
  rw [← List.filter_reverse]
  cases hreverse : lines.reverse with
  | nil => simp only [hreverse] at hend
  | cons line rest =>
    cases line <;> simp_all [List.filter_cons, isLabelHOL, notSkip]

end Flapjack.Compiler.Backend.LabFilter.Proofs
