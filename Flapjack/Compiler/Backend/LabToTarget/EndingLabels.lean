import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.LabelUpdates
import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.Padding
import Flapjack.Compiler.Backend.LabToTarget.SimpleEncoder
import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.Encoding
import Flapjack.Compiler.Backend.LabProps.SectionEnd

/-! Full original ending-label preservation through initial/repeated encoding.
The line theorem retains separate nonempty and LAST-classifier conjuncts.
`lastLabel` uses a checked optional last element; its false empty value is
irrelevant in the tagged theorem because both source and target have the
original nonempty conjunct. It is not a total HOL LAST port. -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.LabProps

/-- Flapjack-specific guarded LAST classifier, without a HOL declaration:
only used alongside the original nonempty guard in tagged statements. -/
def lastLabel {width : Nat} [NeZero width] (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) : Bool :=
  (lines.getLast?.map isLabelHOL).getD false

private theorem sameClassifier {width : Nat} [NeZero width]
    (x y : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) (h : lineSimilar x y) : isLabelHOL x = isLabelHOL y := by
  cases x <;> cases y <;> simp_all [lineSimilar,isLabelHOL]

private theorem similarLastLabel {width : Nat} [NeZero width]
    (xs ys : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (h : LinesRel lineSimilar xs ys) :
    lastLabel xs = lastLabel ys := by
  induction h with
  | nil => rfl
  | @cons x y xs ys hxy htail ih =>
    by_cases hn : xs = []
    · subst xs
      cases htail
      simpa [lastLabel] using sameClassifier x y hxy
    · have hy : ys ≠ [] := by
        intro heq
        subst ys
        cases htail
        contradiction
      simp only [lastLabel,List.getLast?_cons_of_ne_nil hn,List.getLast?_cons_of_ne_nil hy] at ih ⊢
      exact ih

private theorem similarNonempty {width : Nat} [NeZero width]
    (xs ys : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (h : LinesRel lineSimilar xs ys) : xs ≠ [] → ys ≠ [] := by
  cases h <;> simp

private theorem endLabel_iff {width : Nat} [NeZero width] (sec : Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    secEndsWithLabelNative sec ↔ sec.lines ≠ [] ∧ lastLabel sec.lines = true := by
  unfold secEndsWithLabelNative lastLabel
  rw [List.getLast?_eq_head?_reverse]
  have hn : sec.lines ≠ [] ↔ sec.lines.reverse ≠ [] := by simp
  rw [hn]
  cases sec.lines.reverse <;> simp

private theorem similarEnds {width : Nat} [NeZero width]
    (left right : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (h : codeSimilar left right)
    (hs : ∀ sec ∈ left, secEndsWithLabelNative sec) :
    ∀ sec ∈ right, secEndsWithLabelNative sec := by
  induction left generalizing right with
  | nil => cases right <;> simp_all [codeSimilar]
  | cons a tail ih =>
    cases right with
    | nil => simp_all [codeSimilar]
    | cons b rest =>
      have ha := (endLabel_iff a).mp (hs a (by simp))
      have hb : secEndsWithLabelNative b := by
        apply (endLabel_iff b).mpr
        exact ⟨similarNonempty _ _ h.2.1 ha.1,
          (similarLastLabel _ _ h.2.1).symm.trans ha.2⟩
      simpa using And.intro hb (ih rest h.1 (fun sec hm => hs sec (by simp [hm])))

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem encLinesAgainSimp_endsWithLabel {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8)) (ls res : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (ok : Bool) :
    encLinesAgainSimp labs ffis pos enc ls = (res,ok) ∧
      ls ≠ [] ∧ lastLabel ls = true → res ≠ [] ∧ lastLabel res = true := by
  rintro ⟨heq,hne,hlast⟩
  have hacc := encLinesAgainSimp_eq labs ffis pos enc ls [] true
  rw [heq] at hacc
  simp only [List.reverse_nil,List.nil_append,Bool.true_and] at hacc
  have hsimilar : LinesRel lineSimilar ls res :=
    encLinesAgain_implies_similar labs ffis pos enc ls [] true res
      (secLength res pos,ok) [] hacc .nil
  exact ⟨similarNonempty _ _ hsimilar hne,
    (similarLastLabel _ _ hsimilar).symm.trans hlast⟩

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem encSecsAgain_endsWithLabel {width : Nat} [NeZero width]
    (pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8)) (lines res : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (ok : Bool) :
    encSecsAgain pos labs ffis enc lines = (res,ok) ∧
      (∀ sec ∈ lines, secEndsWithLabelNative sec) →
    ∀ sec ∈ res, secEndsWithLabelNative sec := by
  rintro ⟨heq,hs⟩
  exact similarEnds lines res (encSecsAgain_implies_similar pos labs ffis enc lines res ok heq) hs

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem encSecList_endsWithLabel {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (∀ sec ∈ code, secEndsWithLabelNative sec) →
    ∀ sec ∈ encSecList enc code, secEndsWithLabelNative sec := by
  intro hs
  have hr := (codeSimilar_encSecList code code enc).mpr (codeSimilar_refl code)
  exact similarEnds code (encSecList enc code) (codeSimilar_sym _ _ hr) hs


-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem updLabLen_endsWithLabel {width : Nat} [NeZero width]
    (pos : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (∀ sec ∈ code, secEndsWithLabelNative sec) →
    ∀ sec ∈ updLabLen pos code, secEndsWithLabelNative sec := by
  intro hs
  have hr := (codeSimilar_updLabLen code pos code).mpr (codeSimilar_refl code)
  exact similarEnds code (updLabLen pos code) (codeSimilar_sym _ _ hr) hs

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem padCode_endsWithLabel {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (∀ sec ∈ code, secEndsWithLabelNative sec) →
    ∀ sec ∈ padCode nop code, secEndsWithLabelNative sec := by
  intro hs
  exact similarEnds code (padCode nop code)
    (codeSimilar_padCode code code nop (codeSimilar_refl code)) hs

end Flapjack.Compiler.Backend.LabToTarget
