import Flapjack.Compiler.Backend.LabToTarget.OffsetInvariant
import Flapjack.Compiler.Backend.LabToTarget.LabelPosition
import Flapjack.Compiler.Backend.LabToTarget.AddNopProps
import Flapjack.Compiler.Backend.LabToTarget.ZeroPreservation
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Flapjack constructor proof infrastructure for HOL's nonlabel-accumulator
subcase: changing its final forward annotation preserves all earlier offsets.
There is no separately named HOL declaration for this local calculation. -/
private theorem reverseAddNop_invariants {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (aux : List (LabLineHOL width))
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (hn : match (generalizing := false) aux with | [] => False | x :: _ => isLabelHOL x ≠ true)
    (hp : labLenPosOk pos aux.reverse) (ho : linesOffsetOk labs ffis pos aux.reverse) :
    labLenPosOk pos (addNop nop aux).reverse ∧ linesOffsetOk labs ffis pos (addNop nop aux).reverse := by
  cases aux with
  | nil => exact False.elim hn
  | cons x xs =>
    cases x with
    | label k1 k2 len => simp [isLabelHOL] at hn
    | asm a bs len =>
      simpa [addNop,List.reverse_cons,labLenPosOk_append,linesOffsetOk_append,
        labLenPosOk,linesOffsetOk,lineLabLenPosOk,lineOffsetOk] using And.intro hp ho
    | labAsm a w bs len =>
      simpa [addNop,List.reverse_cons,labLenPosOk_append,linesOffsetOk_append,
        labLenPosOk,linesOffsetOk,lineLabLenPosOk,lineOffsetOk] using And.intro hp ho

/-- Flapjack proof infrastructure extracting the source parity clause: at an
even position the next line cannot be a Label with annotation1. -/
private theorem evenParity_notLeadingOne {width : Nat} [NeZero width] (pos : Nat)
    (lines : List (LabLineHOL width)) (he : pos % 2 = 0) (hp : labLenPosOk pos lines) :
    ¬(match (generalizing := false) lines with | .label _ _ len :: _ => len = 1 | _ => False) := by
  cases lines with
  | nil => simp
  | cons x xs =>
    cases x with
    | label k1 k2 len =>
      have hlen : len = 0 := by simpa [lineLabLenPosOk,he] using hp.1
      simp [hlen]
    | asm a bs len => simp
    | labAsm a w bs len => simp

/-- Full original padding offset preservation. Both guarded NULL/HD expressions
are represented by constructor cases, with no empty-head value or total HD. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_offset_ok_pad_section"
  (words_as_type_indexed_bitvec)]
theorem linesOffsetOk_padSection {width : Nat} [NeZero width]
    (nop : List (BitVec 8))
    (lines aux : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat) :
    labLenPosOk (pos+(aux.map lineLen).sum) lines ∧ labLenPosOk pos aux.reverse ∧
    (∀ l ∈ aux,labelZero l) ∧
    ((match (generalizing := false) lines with | .label _ _ len :: _ => len = 1 | _ => False) →
      (match (generalizing := false) aux with | [] => False | x :: _ => isLabelHOL x ≠ true)) ∧
    linesOffsetOk labs ffis pos (aux.reverse++lines) →
      linesOffsetOk labs ffis pos (padSection nop lines aux) := by
  induction lines generalizing aux pos with
  | nil =>
    rintro ⟨_,_,_,_,ho⟩
    simpa [padSection] using ho
  | cons line tail ih =>
    rintro ⟨hp,ha,hzero,hhead,ho⟩
    have hoaux := (linesOffsetOk_append labs ffis pos aux.reverse (line::tail)).1 ho
    have holines : linesOffsetOk labs ffis (pos+(aux.map lineLen).sum) (line::tail) := by
      simpa [List.map_reverse,List.sum_reverse] using hoaux.2
    cases line with
    | asm a bs len =>
      simp only [labLenPosOk,lineLabLenPosOk,lineLen] at hp
      simp only [padSection]
      apply ih
      refine ⟨?_,?_,?_,?_,?_⟩
      · simpa [List.map_cons,List.sum_cons,lineLen,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hp.2
      · simpa [List.reverse_cons,labLenPosOk_append,labLenPosOk,lineLabLenPosOk] using ha
      · simpa [labelZero] using hzero
      · simp [isLabelHOL]
      · simpa [List.reverse_cons,List.append_assoc,linesOffsetOk_append,linesOffsetOk,lineOffsetOk,
          lineLen,List.map_reverse,List.sum_reverse,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ho
    | labAsm a w bs len =>
      simp only [labLenPosOk,lineLabLenPosOk,lineLen] at hp
      simp only [padSection]
      apply ih
      refine ⟨?_,?_,?_,?_,?_⟩
      · simpa [List.map_cons,List.sum_cons,lineLen,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hp.2
      · simpa [List.reverse_cons,labLenPosOk_append,labLenPosOk,lineLabLenPosOk] using ha
      · simpa [labelZero] using hzero
      · simp [isLabelHOL]
      · simpa [List.reverse_cons,List.append_assoc,linesOffsetOk_append,linesOffsetOk,lineOffsetOk,
          lineLen,List.map_reverse,List.sum_reverse,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ho
    | label k1 k2 len =>
      simp only [labLenPosOk,lineLabLenPosOk,lineLen] at hp
      by_cases hz : len = 0
      · subst len
        have he : (pos+(aux.map lineLen).sum) % 2 = 0 := by
          split at hp
          · assumption
          · simp at hp
        simp only [padSection]
        apply ih
        refine ⟨?_,?_,?_,?_,?_⟩
        · simpa [List.map_cons,List.sum_cons,lineLen] using hp.2
        · simpa [List.reverse_cons,labLenPosOk_append,labLenPosOk,lineLabLenPosOk,lineLen,
            List.map_reverse,List.sum_reverse,he] using ha
        · simpa [labelZero] using hzero
        · intro hone
          exact False.elim (evenParity_notLeadingOne _ tail he (by simpa using hp.2) hone)
        · simpa [List.reverse_cons,List.append_assoc,linesOffsetOk_append,linesOffsetOk,lineOffsetOk,
            lineLen,List.map_reverse,List.sum_reverse] using ho
      · have hlen : len = 1 := by split at hp <;> omega
        have hodd : (pos+(aux.map lineLen).sum) % 2 ≠ 0 := by split at hp <;> omega
        have hn : match (generalizing := false) aux with | [] => False | x :: _ => isLabelHOL x ≠ true := hhead hlen
        have hnall : ¬(∀ l ∈ aux,isLabelHOL l = true) := by
          cases aux with
          | nil => exact False.elim hn
          | cons x xs => exact fun h => hn (h x (by simp))
        have hs := lineLen_addNop_nonlabel nop aux hnall
        have he : (pos+((addNop nop aux).map lineLen).sum) % 2 = 0 := by rw [hs]; omega
        have had := reverseAddNop_invariants nop aux labs ffis pos hn ha hoaux.1
        simp only [padSection,if_neg hz]
        apply ih
        refine ⟨?_,?_,?_,?_,?_⟩
        · simpa [List.map_cons,List.sum_cons,lineLen,hs,hlen,Nat.add_assoc] using hp.2
        · simpa [List.reverse_cons,labLenPosOk_append,labLenPosOk,lineLabLenPosOk,lineLen,
            List.map_reverse,List.sum_reverse,he] using had.1
        · simpa [labelZero] using (everyLabelZero_addNop aux nop).2 hzero
        · intro hone
          exact False.elim (evenParity_notLeadingOne _ tail he (by simpa [hs,hlen,Nat.add_assoc] using hp.2) hone)
        · simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
          apply (linesOffsetOk_append labs ffis pos (addNop nop aux).reverse (.label k1 k2 0 :: tail)).2
          refine ⟨had.2,?_⟩
          simpa [linesOffsetOk,lineOffsetOk,lineLen,List.map_reverse,List.sum_reverse,hs,hlen,Nat.add_assoc] using holines
end Flapjack.Compiler.Backend.LabToTarget
