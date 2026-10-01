import Flapjack.Compiler.Backend.LabLang
import Flapjack.Misc.Sptree

/-!
# Faithful Cake label computation (`lab_to_target`)

Exact carriers-witnessed definitions from
`cakeml/compiler/backend/lab_to_targetScript.sml:62-83`.  `section_labels`
folds a section's lines into a `(position, labelled-offset-list)` pair,
ignoring zero labels; `compute_labels_alt` walks the section list and builds
the two-level `spt` mapping each section id to its label offsets, seeded with
the section's start position under key `0`.

The line parameters (`AsmOrCbw`, `AsmWithLab`, `Word`) stay fully
polymorphic, so this module carries no word-width translation.  HOL `insert`
and `fromAList` are the Sptree operations, rendered as `sptInsert` and
`sptFromAList`.

This is the label-computation half of the phase; the offset and
program-transform halves remain to be ported.
-/

namespace Flapjack.Compiler.Backend.LabToTarget

open Flapjack.Compiler.Backend.LabLang
open Flapjack

/-- Exact HOL `lab_to_target$section_labels_def`
(`lab_to_targetScript.sml:62-74`): accumulate byte positions over a section's
lines.  A `Label` with a zero label number is ignored (`if l2 = 0`), otherwise
its `(label, pos + len)` is prepended to the accumulated list; `Asm` and
`LabAsm` advance the position by their fixed `len` without recording a label. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "section_labels_def"]
def sectionLabels {AsmOrCbw AsmWithLab Word : Type} (pos : Nat)
    (lines : List (Line AsmOrCbw AsmWithLab Word))
    (labs : List (Nat × Nat)) : Nat × List (Nat × Nat) :=
  match lines with
  | [] => (pos, labs)
  | .label _ l2 len :: xs =>
      if l2 = 0 then
        sectionLabels (pos + len) xs labs
      else
        sectionLabels (pos + len) xs ((l2, pos + len) :: labs)
  | .asm _ _ len :: xs => sectionLabels (pos + len) xs labs
  | .labAsm _ _ _ len :: xs => sectionLabels (pos + len) xs labs

/-- Exact HOL `lab_to_target$compute_labels_alt_def`
(`lab_to_targetScript.sml:76-83`): for each section, `section_labels` computes
its `(new_pos, sec_labs)` from the running position, and the section id is
mapped to the `spt` built from `(0, pos) :: sec_labs` via `fromAList`, inserted
into the accumulator with `insert`.  The start offset `pos` is captured before
advancing. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "compute_labels_alt_def"]
def computeLabelsAlt {AsmOrCbw AsmWithLab Word : Type} (pos : Nat)
    (sections : List (Section (Line AsmOrCbw AsmWithLab Word)))
    (labs : Spt (Spt Nat)) : Spt (Spt Nat) :=
  match sections with
  | [] => labs
  | sec :: rest =>
      let (newPos, secLabs) := sectionLabels pos sec.lines []
      computeLabelsAlt newPos rest
        (sptInsert sec.sectionId (sptFromAList ((0, pos) :: secLabs)) labs)

end Flapjack.Compiler.Backend.LabToTarget
