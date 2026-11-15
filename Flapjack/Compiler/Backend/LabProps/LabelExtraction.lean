module

public import Flapjack.Compiler.Backend.LabProps.LabelSets
public import Mathlib.Data.Set.Lattice

@[expose] public section

/-! `labPropsScript.sml` label-extraction set facts. The HOL proofs use
`BIGUNION`/`IMAGE`/`set`, so the set lattice lives in this leaf beneath the
`LabProps` counterpart rather than in the `LabelSets` hub. -/

namespace Flapjack.Compiler.Backend.LabProps.LabelSets
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-- Exact HOL `line_get_code_labels_extract_labels` (`labPropsScript.sml:1288`):
the union of every listed line's code-label set is the second component of the
extracted label list. HOL proves it by `recInduct extract_labels_ind`; the Lean
induction is over the same list recursion, with the hypothesis restated in
membership form so the per-line case splits close directly. -/
@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml"
  "line_get_code_labels_extract_labels" (words_as_type_indexed_bitvec)]
theorem lineGetCodeLabels_extractLabels {width : Nat} [NeZero width]
    (l : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    ⋃₀ (lineGetCodeLabels '' {line | line ∈ l}) =
      (Prod.snd '' {p | p ∈ extractLabels l}) := by
  induction l with
  | nil => ext p; simp [extractLabels]
  | cons line xs ih =>
    have ih' : ∀ p : Nat, (∃ x ∈ xs, p ∈ lineGetCodeLabels x) ↔
        (∃ q ∈ extractLabels xs, q.2 = p) := by
      intro p
      have h := congrArg (fun s : Set Nat => p ∈ s) ih
      simpa [Set.mem_sUnion, Set.mem_image] using h
    simp only [lineGetCodeLabels] at ih'
    ext p
    cases line with
    | label l1 l2 len =>
      simp [extractLabels, lineGetCodeLabels, Set.mem_image, ih', eq_comm]
    | asm b bytes len =>
      simp [extractLabels, lineGetCodeLabels, Set.mem_image, ih']
    | labAsm a w bytes len =>
      simp [extractLabels, lineGetCodeLabels, Set.mem_image, ih']

end Flapjack.Compiler.Backend.LabProps.LabelSets
