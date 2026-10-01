import Flapjack.Compiler.Backend.LabLang
import Flapjack.Compiler.Encoders.Asm
import Flapjack.Misc.Sptree

/-!
# Faithful Lab-to-target label computation

Literal ports of the `lab_to_targetScript.sml` label-computation definitions.
HOL `section_labels : num -> α line list -> ...` and
`compute_labels_alt : num -> α sec list -> ...` are polymorphic in the single
word dimension of the native `α line`/`α sec` carriers, whose `asm_or_cbw`,
`asm_with_lab` payloads and `'a word` position all share that one width.
Accordingly these definitions are stated over the canonical native shared-width
line/section (fixed `HolCmp`/`HolMemop`/`HolAsm`/`HolAddr`/`HolRegImm` and the
native `MlString`), qualified with `(words_as_type_indexed_bitvec)`.
-/

namespace Flapjack.Compiler.Backend.LabToTarget

open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-- Exact HOL `section_labels_def`
(`cakeml/compiler/backend/lab_to_targetScript.sml:62-74`). Collects
`(label, position)` pairs inside one section, ignoring zero labels, advancing the
position by each line's length. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "section_labels_def"
  (words_as_type_indexed_bitvec)]
def sectionLabels {width : Nat} [NeZero width] :
    Nat → List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) →
    List (Nat × Nat) → Nat × List (Nat × Nat)
  | pos, [], labs => (pos, labs)
  | pos, .label _ l2 len :: xs, labs =>
      if l2 = 0 then sectionLabels (width := width) (pos + len) xs labs
      else sectionLabels (width := width) (pos + len) xs ((l2, pos + len) :: labs)
  | pos, .asm _ _ len :: xs, labs => sectionLabels (width := width) (pos + len) xs labs
  | pos, .labAsm _ _ _ len :: xs, labs => sectionLabels (width := width) (pos + len) xs labs

/-- Exact HOL `compute_labels_alt_def`
(`cakeml/compiler/backend/lab_to_targetScript.sml:76-83`). Folds
`section_labels` over the sections, inserting each section's label association
list into the section-id-indexed tree map. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "compute_labels_alt_def"
  (words_as_type_indexed_bitvec)]
def computeLabelsAlt {width : Nat} [NeZero width] :
    Nat → List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) →
    Spt (Spt Nat) → Spt (Spt Nat)
  | _, [], labs => labs
  | pos, sec :: rest, labs =>
      let (newPos, secLabs) := sectionLabels (width := width) pos sec.lines []
      computeLabelsAlt (width := width) newPos rest
        (sptInsert sec.sectionId (sptFromAList ((0, pos) :: secLabs)) labs)

end Flapjack.Compiler.Backend.LabToTarget
