import Flapjack.Compiler.Backend.LabProps.SectionEnd

/-! Native kernel replays of lab_props_sec_ends_label_probe.out. -/
namespace Flapjack.Test.LabSectionEndParity
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps
private def labelLine : LabLineHOL 8 := .label 0 1 0
private def asmLine : LabLineHOL 8 := .asm (.asmi (.inst .skip)) [] 0
-- is_label_label
example : isLabelHOL labelLine = true := rfl
-- is_label_asm
example : isLabelHOL asmLine = false := rfl
-- sec_label_end
example : secEndsWithLabelNative (width := 8) ⟨0, [labelLine]⟩ := rfl
-- sec_asm_end
example : ¬ secEndsWithLabelNative (width := 8) ⟨0, [asmLine]⟩ := by
  simp [secEndsWithLabelNative, asmLine, isLabelHOL]
-- sec_empty
example : ¬ secEndsWithLabelNative (width := 8) ⟨0, []⟩ := by
  simp [secEndsWithLabelNative]
end Flapjack.Test.LabSectionEndParity
