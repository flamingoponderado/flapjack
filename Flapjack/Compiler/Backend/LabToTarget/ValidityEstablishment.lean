import Flapjack.Compiler.Backend.LabToTarget.NopInvariant
import Mathlib.Data.Set.Insert
import Flapjack.Compiler.Backend.LabToTarget.EncodingValidity
import Flapjack.Compiler.Backend.LabToTarget.OffsetInvariant
import Flapjack.Compiler.Backend.LabToTarget.LabelExistence
import Flapjack.Compiler.Backend.LabToTarget.StrongEvenLabels
import Flapjack.Compiler.Backend.LabProps.Native
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Misc Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabProps.LabelSets
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Full original establishment theorem, retaining all six source guards. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "line_ok_pre_light_imp_line_ok" (words_as_type_indexed_bitvec)]
theorem lineOk_pre_light_establishes {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (pos : Nat) (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :
    lineOkPreHOL c line ∧ lineEncWithNop c.encode labs ffis pos line ∧
    lineOffsetOk labs ffis pos line ∧ lineLabsExist labs line ∧
    lineOkLight c line = true ∧ (isLabelHOL line = true → pos % 2 = 0) →
      lineOk c labs ffis pos line := by
  rintro ⟨hp,hn,ho,he,hl,hpar⟩
  cases line with
  | label sid lid len => exact ⟨hpar rfl,hn⟩
  | asm a bytes len => exact ⟨hn.1,hn.2,hp⟩
  | labAsm a w bytes len =>
    change w = getJumpOffset a ffis labs pos at ho
    subst w
    cases a with
    | halt =>
      simpa [lineOk,lineEncWithNop,lineOkLight,getJumpOffset,BitVec.zero_sub] using
        And.intro hn.1 (And.intro hn.2 hl)
    | install =>
      simpa [lineOk,lineEncWithNop,lineOkLight,getJumpOffset,BitVec.zero_sub] using
        And.intro hn.1 (And.intro hn.2 hl)
    | callFFI name =>
      simpa [lineOk,lineEncWithNop,lineOkLight,getJumpOffset,BitVec.zero_sub,Nat.add_comm] using
        And.intro hn.1 (And.intro hn.2 hl)
    | call label => simp [lineOkLight] at hl
    | jump label =>
      cases label with
      | lab k1 k2 =>
        cases hlookup : labLookup k1 k2 labs with
        | none =>
          exact False.elim (he k1 k2 (by simp [labsOf]) hlookup)
        | some target =>
          have hf := labLookup_implies_findPos k1 k2 labs target hlookup
          simpa [lineOk,lineEncWithNop,lineOkLight,getJumpOffset,getLabel,labInst,
            hlookup,hf,BitVec.sub_eq_add_neg] using And.intro hn.1 (And.intro hn.2 hl)
    | jumpCmp cmp reg imm label =>
      cases label with
      | lab k1 k2 =>
        cases hlookup : labLookup k1 k2 labs with
        | none =>
          exact False.elim (he k1 k2 (by simp [labsOf]) hlookup)
        | some target =>
          have hf := labLookup_implies_findPos k1 k2 labs target hlookup
          simpa [lineOk,lineEncWithNop,lineOkLight,getJumpOffset,getLabel,labInst,
            hlookup,hf,BitVec.sub_eq_add_neg] using And.intro hn.1 (And.intro hn.2 hl)
    | locValue reg label =>
      cases label with
      | lab k1 k2 =>
        cases hlookup : labLookup k1 k2 labs with
        | none =>
          exact False.elim (he k1 k2 (by simp [labsOf]) hlookup)
        | some target =>
          have hf := labLookup_implies_findPos k1 k2 labs target hlookup
          simpa [lineOk,lineEncWithNop,lineOkLight,getJumpOffset,getLabel,labInst,
            hlookup,hf,BitVec.sub_eq_add_neg] using And.intro hn.1 (And.intro hn.2 hl)
/-- Flapjack induction infrastructure: remove a consumed line from EVERY
section/line membership. This has no independently named HOL original. -/
private theorem sectionEvery_tail {width : Nat} [NeZero width]
    (pred : LabLineHOL width → Prop) (k : Nat) (line : LabLineHOL width)
    (lines : List (LabLineHOL width)) (rest : List (Section (LabLineHOL width)))
    (h : ∀ sec ∈ (⟨k,line::lines⟩::rest : List (Section (LabLineHOL width))),
      ∀ l ∈ sec.lines,pred l) :
    ∀ sec ∈ (⟨k,lines⟩::rest : List (Section (LabLineHOL width))),∀ l ∈ sec.lines,pred l := by
  intro sec hm
  rcases List.mem_cons.mp hm with rfl | hm
  · intro l hl
    exact h ⟨k,line::lines⟩ (by simp) l (List.mem_cons_of_mem line hl)
  · exact h sec (List.mem_cons_of_mem _ hm)

/-- Flapjack infrastructure: derive annotation/physical agreement from the
original NOP invariant, rather than assuming the target line validity. -/
private theorem nop_annotationLength {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (pos : Nat) (line : LabLineHOL width) (h : lineEncWithNop c.encode labs ffis pos line) :
    lineLength line = lineLen line := by
  have hl := lineEncWithNop_lengthOk c.encode labs ffis pos line h
  cases line with
  | label sid lid len =>
    have hz : len = 0 := by simpa [lineLengthOk,lineBytes,lineLen] using hl.symm
    simp [lineLength,lineLen,hz]
  | asm _ _ _ => simpa [lineLengthOk,lineBytes,lineLength,lineLen] using hl
  | labAsm _ _ _ _ => simpa [lineLengthOk,lineBytes,lineLength,lineLen] using hl

/-- Full original code-level establishment with all six source invariants.
The strong evenness guard includes empty-section end parity. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "all_enc_ok_pre_light_imp_all_enc_ok" (words_as_type_indexed_bitvec)]
theorem allEncOk_pre_light_establishes {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (pos : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    allEncWithNop c.encode labs ffis pos code ∧ allEncOkPreHOL c code ∧
    allEncOkLight c code = true ∧ evenLabelsStrong pos code ∧
    allLabsExist labs code ∧ offsetOk labs ffis pos code → allEncOk c labs ffis pos code := by
  induction code generalizing pos with
  | nil => simp [allEncOk]
  | cons sec rest ih =>
    rcases sec with ⟨k,lines⟩
    induction lines generalizing pos with
    | nil =>
      rintro ⟨hn,hp,hl,hs,he,ho⟩
      have hpRest : allEncOkPreHOL c rest := fun sec hm => hp sec (by simp [hm])
      have heRest : allLabsExist labs rest := fun sec hm => he sec (by simp [hm])
      have hlRest : allEncOkLight c rest = true := by
        simpa [allEncOkLight,secOkLight] using hl
      simp only [allEncWithNop] at hn
      simp only [evenLabelsStrong] at hs
      simp only [offsetOk,linesOffsetOk,List.map_nil,List.sum_nil,Nat.add_zero,true_and] at ho
      rw [allEncOk]
      exact ⟨hs.1,ih pos ⟨hn,hpRest,hlRest,hs.2,heRest,ho⟩⟩
    | cons line lines ihLines =>
      rintro ⟨hn,hp,hl,hs,he,ho⟩
      have hpHead := hp ⟨k,line::lines⟩ (by simp) line (by simp)
      have heHead := he ⟨k,line::lines⟩ (by simp) line (by simp)
      have hpTail : allEncOkPreHOL c (⟨k,lines⟩::rest) :=
        sectionEvery_tail (lineOkPreHOL c) k line lines rest hp
      have heTail : allLabsExist labs (⟨k,lines⟩::rest) :=
        sectionEvery_tail (lineLabsExist labs) k line lines rest he
      have hlEvery : ∀ sec ∈ (⟨k,line::lines⟩::rest : List (Section (LabLineHOL width))),
          ∀ l ∈ sec.lines,lineOkLight c l = true := by
        simpa only [allEncOkLight,secOkLight,List.all_eq_true] using hl
      have hlHead := hlEvery ⟨k,line::lines⟩ (by simp) line (by simp)
      have hlTail : allEncOkLight c (⟨k,lines⟩::rest) = true := by
        simpa only [allEncOkLight,secOkLight,List.all_eq_true] using
          sectionEvery_tail (fun l => lineOkLight c l = true) k line lines rest hlEvery
      rw [allEncWithNop] at hn
      rcases hn with ⟨hnHead,hnTail⟩
      rw [evenLabelsStrong] at hs
      rcases hs with ⟨hsHead,hsTail⟩
      rw [offsetOk] at ho
      rcases ho with ⟨hoLines,hoRest⟩
      rw [linesOffsetOk] at hoLines
      rcases hoLines with ⟨hoHead,hoTail⟩
      have hlength := nop_annotationLength c labs ffis pos line hnHead
      have hoNew : offsetOk labs ffis (pos + lineLen line) (⟨k,lines⟩::rest) := by
        exact ⟨hoTail,by simpa [List.map_cons,List.sum_cons,Nat.add_assoc] using hoRest⟩
      rw [allEncOk]
      refine ⟨lineOk_pre_light_establishes c labs ffis pos line
        ⟨hpHead,hnHead,hoHead,heHead,hlHead,hsHead⟩,?_⟩
      apply ihLines (pos + lineLength line)
      exact ⟨hnTail,hpTail,hlTail,by simpa [hlength] using hsTail,heTail,
        by simpa [hlength] using hoNew⟩
end Flapjack.Compiler.Backend.LabToTarget
