import Flapjack.Compiler.Backend.LabLang
import Flapjack.Misc.Sptree

/-!
# Faithful Lab-to-target label computation

Literal ports of the `lab_to_targetScript.sml` label-computation definitions
over the faithful `LabLang` carriers. Both definitions are polymorphic in the
`Line` parameters and do not mention the word carrier, so they need no word
qualifier.
-/

namespace Flapjack.Compiler.Backend.LabToTarget

open Flapjack.Compiler.Backend.LabLang

/-- Exact HOL `section_labels_def`
(`cakeml/compiler/backend/lab_to_targetScript.sml:62-74`). Collects
`(label, position)` pairs inside one section, ignoring zero labels, advancing the
position by each line's length. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "section_labels_def"]
def sectionLabels {AsmOrCbw AsmWithLab Word : Type} :
    Nat → List (Line AsmOrCbw AsmWithLab Word) → List (Nat × Nat) → Nat × List (Nat × Nat)
  | pos, [], labs => (pos, labs)
  | pos, .label _ l2 len :: xs, labs =>
      if l2 = 0 then sectionLabels (pos + len) xs labs
      else sectionLabels (pos + len) xs ((l2, pos + len) :: labs)
  | pos, .asm _ _ len :: xs, labs => sectionLabels (pos + len) xs labs
  | pos, .labAsm _ _ _ len :: xs, labs => sectionLabels (pos + len) xs labs

/-- Exact HOL `compute_labels_alt_def`
(`cakeml/compiler/backend/lab_to_targetScript.sml:76-83`). Folds
`section_labels` over the sections, inserting each section's label association
list into the section-id-indexed tree map. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "compute_labels_alt_def"]
def computeLabelsAlt {AsmOrCbw AsmWithLab Word : Type} :
    Nat → List (Section (Line AsmOrCbw AsmWithLab Word)) → Spt (Spt Nat) → Spt (Spt Nat)
  | _, [], labs => labs
  | pos, sec :: rest, labs =>
      let (newPos, secLabs) := sectionLabels pos sec.lines []
      computeLabelsAlt newPos rest
        (sptInsert sec.sectionId (sptFromAList ((0, pos) :: secLabs)) labs)

end Flapjack.Compiler.Backend.LabToTarget
