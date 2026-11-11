module

public import Flapjack.Compiler.Backend.LabToTarget.Labels
public import Flapjack.Compiler.Backend.LabProps.LabelSets
public import Mathlib.Data.Set.Insert

@[expose] public section
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.LabProps.LabelSets

/-- Full original extraction theorem: both zero insertions and the arbitrary
label accumulator are retained. The only premise is the actual returned tuple. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "section_labels_line_get_code_labels" (words_as_type_indexed_bitvec)]
theorem sectionLabels_codeLabels {width : Nat} [NeZero width] (pos : Nat)
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (aux : List (Nat × Nat)) (newPos : Nat) (labs : List (Nat × Nat)) :
    sectionLabels pos lines aux = (newPos,labs) →
      insert 0 {key | key ∈ labs.map Prod.fst} =
        insert 0 {key | key ∈ aux.map Prod.fst} ∪
          {key | ∃ l ∈ lines,key ∈ lineGetCodeLabels l} := by
  revert newPos labs
  fun_induction sectionLabels pos lines aux <;> simp_all [lineGetCodeLabels]
  all_goals
    intro _ _ _
    ext key
    simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_ofPred_eq]
    grind
end Flapjack.Compiler.Backend.LabToTarget
