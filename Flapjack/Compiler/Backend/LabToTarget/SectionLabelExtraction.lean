import Flapjack.Compiler.Backend.LabToTarget.Labels
import Flapjack.Compiler.Backend.LabProps.LabelSets
import Mathlib.Data.Set.Insert
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
  induction lines generalizing pos aux with
  | nil =>
    intro heq
    have hl := congrArg Prod.snd heq
    simp only [sectionLabels] at hl
    subst labs
    ext key
    simp
  | cons line tail ih =>
    cases line with
    | label k1 k2 len =>
      intro heq
      by_cases hz : k2 = 0
      · simp only [sectionLabels,hz,if_true] at heq
        have hh := ih (pos+len) aux heq
        ext key
        have hk := congrArg (fun s : Set Nat => key ∈ s) hh
        simp [Set.mem_insert_iff,Set.mem_union,lineGetCodeLabels,hz] at hk ⊢
        constructor
        · intro h
          rcases hk.mp h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · intro h
          rcases h with h | h0 | ht
          · exact hk.mpr (Or.inl h)
          · exact hk.mpr (Or.inl (Or.inl h0))
          · exact hk.mpr (Or.inr ht)
      · simp only [sectionLabels,hz,if_false] at heq
        have hh := ih (pos+len) ((k2,pos+len)::aux) heq
        ext key
        have hk := congrArg (fun s : Set Nat => key ∈ s) hh
        simp [Set.mem_insert_iff,Set.mem_union,lineGetCodeLabels] at hk ⊢
        simpa only [or_assoc,or_left_comm,or_comm] using hk
    | asm a bs len =>
      intro heq
      have hh := ih (pos+len) aux heq
      ext key
      have hk := congrArg (fun s : Set Nat => key ∈ s) hh
      simpa [Set.mem_insert_iff,Set.mem_union,lineGetCodeLabels] using hk
    | labAsm a w bs len =>
      intro heq
      have hh := ih (pos+len) aux heq
      ext key
      have hk := congrArg (fun s : Set Nat => key ∈ s) hh
      simpa [Set.mem_insert_iff,Set.mem_union,lineGetCodeLabels] using hk
end Flapjack.Compiler.Backend.LabToTarget
