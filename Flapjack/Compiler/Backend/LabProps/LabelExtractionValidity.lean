import Flapjack.Compiler.Backend.LabProps.Labels
import Flapjack.Compiler.Backend.LabProps.LabelSets

namespace Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString LabelSets

/-- Both source guards establish the owning section and nonzero label ID.
No distinctness or label-length premise is required. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem secLabelOk_extractLabels {width : Nat} [NeZero width]
    (sectionId : Nat)
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (extractedSection labelId : Nat) :
    (∀ line ∈ lines, secLabelOk sectionId line) ∧
      (extractedSection, labelId) ∈ extractLabels lines →
    extractedSection = sectionId ∧ labelId ≠ 0 := by
  induction lines with
  | nil => simp [extractLabels]
  | cons line rest ih =>
    rintro ⟨hall, hmem⟩
    have ht : ∀ line ∈ rest, secLabelOk sectionId line :=
      fun line h => hall line (List.mem_cons_of_mem _ h)
    cases line with
    | label sid lid len =>
      simp only [extractLabels, List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · cases heq
        exact hall (.label extractedSection labelId len) (by simp)
      · exact ih ⟨ht, hmem⟩
    | asm instruction bytes len => exact ih ⟨ht, hmem⟩
    | labAsm instruction word bytes len => exact ih ⟨ht, hmem⟩

end Flapjack.Compiler.Backend.LabProps
