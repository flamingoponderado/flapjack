import Mathlib.Data.Set.Insert
import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.LabelSets
namespace Flapjack.Test.LabToTargetSimilarLabelsParity
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabProps.LabelSets
private def leftCode : LabProgHOL 8 :=
  [⟨10,[.label 99 7 5,.labAsm (.jump (.lab 3 4)) 123 [] 0,
    .labAsm (.call (.lab 8 9)) 0 [] 0,.label 10 7 0]⟩,⟨20,[]⟩]
private def rightCode : LabProgHOL 8 :=
  [⟨10,[.label 99 7 0,.labAsm (.jump (.lab 3 4)) 9 [255] 37,
    .labAsm (.call (.lab 8 9)) 8 [1,2] 2,.label 10 7 99]⟩,⟨20,[]⟩]
private theorem similar : codeSimilar leftCode rightCode := by
  refine ⟨⟨trivial, .nil, rfl⟩, ?_, rfl⟩
  exact .cons ⟨rfl,rfl⟩ (.cons rfl (.cons rfl (.cons ⟨rfl,rfl⟩ .nil)))
example : codeSimilar leftCode rightCode := similar
example : rightCode.map Section.sectionId = [10,20] := rfl
example : rightCode.map (fun sec => extractLabels sec.lines) = [[(99,7),(10,7)],[]] := rfl
example : (3,4) ∈ getLabels rightCode := by
  simp [getLabels,secGetLabels,lineGetLabels,labsOf,rightCode]
example : (8,9) ∉ getLabels rightCode := by
  simp [getLabels,secGetLabels,lineGetLabels,labsOf,rightCode]
example : (10,7) ∈ getCodeLabels rightCode := by
  simp [getCodeLabels,secGetCodeLabels,lineGetCodeLabels,rightCode]
example : (99,7) ∉ getCodeLabels rightCode := by
  simp [getCodeLabels,secGetCodeLabels,lineGetCodeLabels,rightCode]
example : (20,0) ∈ getCodeLabels rightCode := by
  simp [getCodeLabels,secGetCodeLabels,lineGetCodeLabels,rightCode]
example : codeSimilar leftCode rightCode →
    leftCode.map Section.sectionId = rightCode.map Section.sectionId :=
  codeSimilar_sectionNumbers _ _
example : codeSimilar leftCode rightCode →
    leftCode.map (fun sec => extractLabels sec.lines) =
      rightCode.map (fun sec => extractLabels sec.lines) := codeSimilar_extractedLabels _ _
example : codeSimilar leftCode rightCode →
    getCodeLabels leftCode = getCodeLabels rightCode := codeSimilar_codeLabels _ _
example : codeSimilar leftCode rightCode →
    getLabels leftCode = getLabels rightCode := codeSimilar_labels _ _
example : lineSimilar (width := 8) (.label 99 7 5) (.label 99 7 0) →
    lineGetCodeLabels (width := 8) (.label 99 7 5) =
      lineGetCodeLabels (width := 8) (.label 99 7 0) := lineSimilar_codeLabels _ _
example : lineSimilar (width := 8) (.labAsm (.jump (.lab 3 4)) 123 [] 0)
    (.labAsm (.jump (.lab 3 4)) 9 [255] 37) →
    lineGetLabels (width := 8) (.labAsm (.jump (.lab 3 4)) 123 [] 0) =
      lineGetLabels (width := 8) (.labAsm (.jump (.lab 3 4)) 9 [255] 37) := lineSimilar_labels _ _
example : ¬lineSimilar (width := 8) (.labAsm (.jump (.lab 3 4)) 123 [] 0)
    (.labAsm (.jump (.lab 3 5)) 123 [] 0) := by simp [lineSimilar]
example {width : Nat} [NeZero width] (x y : LabProgHOL width) :
    codeSimilar x y → x.map Section.sectionId = y.map Section.sectionId := codeSimilar_sectionNumbers x y
example {width : Nat} [NeZero width] (x y : LabProgHOL width) :
    codeSimilar x y → x.map (fun sec => extractLabels sec.lines) = y.map (fun sec => extractLabels sec.lines) := codeSimilar_extractedLabels x y
example {width : Nat} [NeZero width] (x y : LabLineHOL width) :
    lineSimilar x y → lineGetCodeLabels x = lineGetCodeLabels y := lineSimilar_codeLabels x y
example {width : Nat} [NeZero width] (x y : LabProgHOL width) :
    codeSimilar x y → getCodeLabels x = getCodeLabels y := codeSimilar_codeLabels x y
example {width : Nat} [NeZero width] (x y : LabLineHOL width) :
    lineSimilar x y → lineGetLabels x = lineGetLabels y := lineSimilar_labels x y
example {width : Nat} [NeZero width] (x y : LabProgHOL width) :
    codeSimilar x y → getLabels x = getLabels y := codeSimilar_labels x y
def runChecks : IO Bool := do
  IO.println "PASS full CodeSimilar label preservation (15 original observations, 6 generic consumers)"
  return true
end Flapjack.Test.LabToTargetSimilarLabelsParity
