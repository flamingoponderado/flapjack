import Flapjack.Compiler.Backend.LabToTarget.Labels
import Flapjack.Compiler.Backend.LabProps.LabelSets

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend.LabProps.LabelSets

/-- The source nonmembership guard preserves the entire accumulator lookup,
including absence and duplicate accumulator entries, at arbitrary positions. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "ALOOKUP_section_labels_ignore" (words_as_type_indexed_bitvec)]
theorem sectionLabels_lookup_ignore {width : Nat} [NeZero width] (pos : Nat)
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (acc : List (Nat × Nat)) (key : Nat) :
    key ∉ (extractLabels lines).map Prod.snd →
    sptAListLookup key (sectionLabels pos lines acc).2 = sptAListLookup key acc := by
  induction lines generalizing pos acc with
  | nil => simp [sectionLabels]
  | cons line rest ih =>
    cases line with
    | label sid lid len =>
      simp only [extractLabels, List.map_cons, List.mem_cons, not_or]
      rintro ⟨hne, ht⟩
      by_cases hz : lid = 0
      · simpa [sectionLabels, hz] using ih (pos + len) acc ht
      · simpa [sectionLabels, hz, sptAListLookup, hne] using
          ih (pos + len) ((lid, pos + len) :: acc) ht
    | asm instruction bytes len =>
      simpa [extractLabels, sectionLabels] using ih (pos + len) acc
    | labAsm instruction word bytes len =>
      simpa [extractLabels, sectionLabels] using ih (pos + len) acc

end Flapjack.Compiler.Backend.LabToTarget
