import Flapjack.Compiler.Backend.LabToTarget.Navigation
import Flapjack.Compiler.Backend.LabProps.Labels
import Flapjack.Compiler.Backend.LabProps.LabelSets

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabProps.LabelSets
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Full original extracted-label existence result. Validity and actual label
membership are the original source hypotheses; the PC is derived. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "extract_labels_loc_to_pc" (words_as_type_indexed_bitvec)]
theorem extractLabels_locToPc {width : Nat} [NeZero width] (l1 l2 : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (∀ sec ∈ code, secLabelsOk sec) ∧
      (l1, l2) ∈ code.flatMap (fun sec => extractLabels sec.lines) →
      ∃ y, locToPc l1 l2 code = some y := by
  induction code with
  | nil => simp
  | cons sec rest ih =>
    rcases sec with ⟨sid, lines⟩
    rintro ⟨hv, hm⟩
    have ht : ∀ sec ∈ rest, secLabelsOk sec := fun sec hs => hv sec (List.mem_cons_of_mem _ hs)
    have hl : ∀ line ∈ lines, secLabelOk sid line := by
      exact hv ⟨sid, lines⟩ (by simp)
    clear hv
    revert hm hl
    induction lines with
    | nil =>
      intro hm hl
      by_cases hh : sid = l1 ∧ l2 = 0
      · exact ⟨0, by rw [locToPc.eq_def]; simp [hh]⟩
      · have hr := ih ⟨ht, by simpa [extractLabels] using hm⟩
        simpa [locToPc, hh] using hr
    | cons line lines ihlines =>
      intro hm hl
      have htail : ∀ x ∈ lines, secLabelOk sid x := fun x hx => hl x (List.mem_cons_of_mem _ hx)
      by_cases hh : sid = l1 ∧ l2 = 0
      · exact ⟨0, by rw [locToPc.eq_def]; simp [hh]⟩
      · cases line with
        | label s l n =>
          by_cases hmch : s = l1 ∧ l = l2 ∧ l2 ≠ 0
          · rcases hmch with ⟨rfl, rfl, hn⟩
            exact ⟨0, by simp [locToPc, hn]⟩
          · have hhead := hl (.label s l n) (by simp)
            have hmem : (l1,l2) ∈ extractLabels lines ++ rest.flatMap (fun sec => extractLabels sec.lines) := by
              simp only [secLabelOk] at hhead
              simp only [List.flatMap_cons, extractLabels, List.cons_append, List.mem_cons] at hm
              rcases hm with he | he
              · have he1 := congrArg Prod.fst he
                have he2 := congrArg Prod.snd he
                simp only at he1 he2
                exact False.elim (hmch ⟨he1.symm, he2.symm, he2 ▸ hhead.2⟩)
              · exact he
            have hr := ihlines (by simpa using hmem) htail
            have hnmatch : ¬ ((s = l1 ∧ l = l2) ∧ l2 ≠ 0) := fun h => hmch ⟨h.1.1, h.1.2, h.2⟩
            simpa [locToPc, hh, isLabelHOL, hnmatch, Bool.and_eq_true] using hr
        | asm inst bytes len =>
          have hr := ihlines (by simpa [extractLabels] using hm) htail
          rcases hr with ⟨y, hy⟩
          exact ⟨y+1, by simp [locToPc, hh, isLabelHOL, hy]⟩
        | labAsm inst word bytes len =>
          have hr := ihlines (by simpa [extractLabels] using hm) htail
          rcases hr with ⟨y, hy⟩
          exact ⟨y+1, by simp [locToPc, hh, isLabelHOL, hy]⟩

end Flapjack.Compiler.Backend.LabToTarget
