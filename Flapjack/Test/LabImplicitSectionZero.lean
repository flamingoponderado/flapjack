import Flapjack.RiscV.LabDiagnostics
import Flapjack.RiscV.Encoding

namespace Flapjack.Test.LabImplicitSectionZero
open Flapjack Flapjack.RiscV

-- Arbitrary sections have a section-zero entry even when no line declares it.
example {width : Nat} (base : Nat) (s : LabSection (Word width)) (rest : LabProgram (Word width)) :
    (labCollectProgramLabels base (s :: rest)).head? = some (s.name, 0, base) := by
  simp [labCollectProgramLabels]
example {width : Nat} [NeZero width] (context : WordFfiContext) (base : Nat)
    (guess : LabLabelIndex) (s : LabSection (Word width)) (rest : LabProgram (Word width)) :
    (labCollectProgramLabelsWithContext context base guess (s :: rest)).head? =
      some (s.name, 0, base) := by simp [labCollectProgramLabelsWithContext]

-- Explicit local zero at a later byte position never replaces the section base.
example : labCollectProgramLabels (width := 64) 1000
    [⟨7, [.asm (.const 2 17) [] 0, .label 123 0 0, .label 7 2 0]⟩] =
    [(7, 0, 1000), (7, 2, 1004)] := by
  simp [labCollectProgramLabels, labCollectLabels,
    labLineInstructionCount, labConstInstructionCount]
example : labCollectProgramLabels (width := 64) 1000
    [⟨7, [.asm (.const 2 17) [] 0]⟩,
     ⟨17, [.asm (.const 3 29) [] 0, .label 999 0 0, .label 17 2 0]⟩] =
    [(7, 0, 1000), (17, 0, 1004), (17, 2, 1008)] := by
  simp [labCollectProgramLabels, labCollectLabels, labSectionInstructionCount,
    labLineInstructionCount, labConstInstructionCount]
example : labCollectProgramLabels (width := 1) 17 [⟨7, []⟩] = [(7, 0, 17)] := by
  simp [labCollectProgramLabels, labCollectLabels]
example : labCollectProgramLabels (width := 80) 17 [⟨7, []⟩, ⟨29, []⟩] =
    [(7, 0, 17), (29, 0, 17)] := by simp [labCollectProgramLabels, labCollectLabels, labSectionInstructionCount]
example : labCollectLabels (width := 64) 7 17 [.label 123 0 0, .label 123 2 0] = [(2, 17)] := by
  simp [labCollectLabels]
example : labCollectLabelsWithContext (width := 64) {services := []} 7 [] 17
    [.label 123 0 0, .label 123 2 0] = [(2, 17)] := by simp [labCollectLabelsWithContext]

-- Actual instruction emission: direct section-zero call needs no entry alias.
theorem crossSectionNoEntry : compileLabProgram (width := 64) {services := []}
    [⟨1, [.labAsm (.jump ⟨2, 0⟩) [] 0]⟩,
     ⟨2, [.asm (.const 1 7) [] 0]⟩] =
    some [.jal 0 4, .ori 1 0 7] := by
  simp [compileLabProgram, labCollectProgramLabels, labCollectProgramLabelsStable,
    labCollectProgramLabelsWithContext, labCollectProgramSectionLabels,
    labSectionCompiledInstructionCount, labProgramLineCompiledInstructionCount,
    labCollectLabels, labSectionInstructionCount, labCompileProgramSections,
    labCompileProgramLines, labCompileAsmProgram, labCompilePlain,
    labLookupProgramPosition, labResolveProgramRef, labLabelIndexOf,
    labOffset, labJumpInstructions, labJumpOffsetFits]
  rfl

-- Both actual single-section entrypoints receive the same implicit zero.
example : compileLabSection (width := 64) {services := []}
    ⟨7, [.labAsm (.jump ⟨7, 0⟩) [] 0]⟩ = some [.jal 0 0] := by
  simp [compileLabSection, labCollectLabelsStable, labCollectLabelsWithContext,
    labCollectLabels, labCompileLines, labCompileAsm,
    labResolveRef, labLookupPosition, labJumpInstructions, labOffset, labJumpOffsetFits]
example : compileLabSectionChecked (width := 64) {services := []}
    ⟨7, [.labAsm (.jump ⟨7, 0⟩) [] 0]⟩ = .ok [.jal 0 0] := by
  simp [compileLabSectionChecked, labCompileLinesChecked,
    labCompileAsmChecked, labCompileAsm, labResolveRef, labLookupPosition,
    labJumpInstructions, labOffset, labJumpOffsetFits]

-- Original riscv_ast/riscv_encode bytes, following original section-zero resolution.
example : (compileLabProgram (width := 64) {services := []}
    [⟨1, [.labAsm (.jump ⟨2, 0⟩) [] 0]⟩,
     ⟨2, [.asm (.const 1 7) [] 0]⟩]).map
    (fun code => (encodeInstructions code).map BitVec.toNat) =
      some [111, 0, 64, 0, 147, 96, 112, 0] := by
  rw [crossSectionNoEntry]
  decide

end Flapjack.Test.LabImplicitSectionZero
