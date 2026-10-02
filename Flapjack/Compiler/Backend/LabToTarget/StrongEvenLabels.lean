import Flapjack.Compiler.Backend.LabToTarget.EvenLabels
import Flapjack.Compiler.Backend.LabToTarget.PositionAppend
import Flapjack.Compiler.Backend.LabProps.SectionEnd
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Flapjack proof infrastructure: removing a first line from a nonempty tail
preserves the actual last-label classification. No independently named HOL original. -/
private theorem endingLabel_tail {width : Nat} [NeZero width] (k : Nat)
    (line : LabLineHOL width) (tail : List (LabLineHOL width)) (hne : tail ≠ []) :
    secEndsWithLabelNative (⟨k,line::tail⟩ : Section (LabLineHOL width)) →
      secEndsWithLabelNative (⟨k,tail⟩ : Section (LabLineHOL width)) := by
  cases hr : tail.reverse with
  | nil =>
    have ht : tail = [] := List.reverse_eq_nil_iff.mp hr
    exact False.elim (hne ht)
  | cons last rest =>
    simp [secEndsWithLabelNative,List.reverse_cons,hr]

/-- Flapjack local induction infrastructure for the original section case.
The tail implication is exactly the outer structural induction hypothesis. -/
private theorem strengthenSection {width : Nat} [NeZero width] (k : Nat)
    (lines : List (LabLineHOL width)) (rest : List (Section (LabLineHOL width)))
    (ihRest : ∀ pos,evenLabels pos rest → evenLabelsStrong pos rest) (pos : Nat) :
    secEndsWithLabelNative (⟨k,lines⟩ : Section (LabLineHOL width)) ∧
    (∀ l ∈ lines,labelZero l) ∧ evenLabels pos (⟨k,lines⟩::rest) →
      evenLabelsStrong pos (⟨k,lines⟩::rest) := by
  induction lines generalizing pos with
  | nil => simp [secEndsWithLabelNative]
  | cons line lines ih =>
    rintro ⟨he,hz,hw⟩
    have hzero := hz line (by simp)
    have htail : ∀ l ∈ lines,labelZero l := fun l hm => hz l (by simp [hm])
    rw [evenLabels] at hw
    rw [evenLabelsStrong]
    refine ⟨hw.1,?_⟩
    cases lines with
    | nil =>
      have hlabel : isLabelHOL line = true := by simpa [secEndsWithLabelNative] using he
      cases line with
      | label sid lid len =>
        simp only [labelZero] at hzero
        subst len
        have hp := hw.1 hlabel
        have ht : evenLabels pos rest := by simpa [lineLen,evenLabels] using hw.2
        simpa [lineLen,evenLabelsStrong] using And.intro hp (ihRest pos ht)
      | asm _ _ _ => simp [isLabelHOL] at hlabel
      | labAsm _ _ _ _ => simp [isLabelHOL] at hlabel
    | cons next tail =>
      exact ih (pos + lineLen line)
        ⟨endingLabel_tail k line (next::tail) (by simp) he,htail,hw.2⟩

/-- Full original weak-to-strong theorem: ending Label and zero annotation
establish even section ends, with exactly the three original guards. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "even_labels_ends_imp_strong" (words_as_type_indexed_bitvec)]
theorem evenLabels_ends_imp_strong {width : Nat} [NeZero width] (pos : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    evenLabels pos code ∧ (∀ sec ∈ code,secEndsWithLabelNative sec) ∧
      (∀ sec ∈ code,secLabelZero sec) → evenLabelsStrong pos code := by
  induction code generalizing pos with
  | nil => simp [evenLabelsStrong]
  | cons sec rest ih =>
    rcases sec with ⟨k,lines⟩
    rintro ⟨hw,he,hz⟩
    have hends : ∀ sec ∈ rest,secEndsWithLabelNative sec := fun sec hm => he sec (by simp [hm])
    have hzero : ∀ sec ∈ rest,secLabelZero sec := fun sec hm => hz sec (by simp [hm])
    exact strengthenSection k lines rest (fun p hp => ih p ⟨hp,hends,hzero⟩) pos
      ⟨he ⟨k,lines⟩ (by simp),hz ⟨k,lines⟩ (by simp),hw⟩
end Flapjack.Compiler.Backend.LabToTarget
