import Flapjack.Compiler.Backend.LabToTarget.LabelPositionPrefix
import Flapjack.Compiler.Backend.LabToTarget.AddNopProps
import Flapjack.Compiler.Backend.LabToTarget.ZeroPreservation
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Flapjack proof infrastructure for the original padding subcase: modifying
its last forward nonlabel cannot affect any subsequent label, since none follow.
There is no separately named HOL theorem for this constructor calculation. -/
private theorem reverseAddNop_posOk {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (aux : List (LabLineHOL width)) (pos : Nat)
    (hn : match aux with | [] => False | x :: _ => isLabelHOL x ≠ true)
    (hp : labLenPosOk pos aux.reverse) : labLenPosOk pos (addNop nop aux).reverse := by
  cases aux with
  | nil => exact False.elim hn
  | cons x xs =>
    cases x with
    | label k1 k2 len => simp [isLabelHOL] at hn
    | asm a bytes len =>
      simpa [addNop,List.reverse_cons,labLenPosOk_append,labLenPosOk,lineLabLenPosOk] using hp
    | labAsm a w bytes len =>
      simpa [addNop,List.reverse_cons,labLenPosOk_append,labLenPosOk,lineLabLenPosOk] using hp

/-- Full source padding parity statement. The literal NULL-or-label-head guard
is represented by cases: empty is True; a nonempty list observes its head.
Thus the source's masked empty HD is never evaluated or assigned a default. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pad_section_pos_ok"
  (words_as_type_indexed_bitvec)]
theorem padSection_posOk {width : Nat} [NeZero width]
    (nop : List (BitVec 8))
    (lines aux : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (pos : Nat) :
    labLenPosOk (pos + (aux.map lineLen).sum) lines ∧
    labLenPosOk pos aux.reverse ∧ (∀ line ∈ aux, labelZero line) ∧
    ((match aux with | [] => True | x :: _ => isLabelHOL x = true) → labelPrefixZero lines) →
      labLenPosOk pos (padSection nop lines aux) := by
  induction lines generalizing aux pos with
  | nil => exact fun h => h.2.1
  | cons line tail ih =>
    rintro ⟨hp,ha,hzero,hguard⟩
    cases line with
    | asm a bytes len =>
      simp only [labLenPosOk,lineLabLenPosOk,lineLen] at hp
      simp only [padSection]
      apply ih
      refine ⟨?_,?_,?_,?_⟩
      · simpa [List.map_cons,List.sum_cons,lineLen,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hp.2
      · simpa [List.reverse_cons,labLenPosOk_append,labLenPosOk,lineLabLenPosOk] using ha
      · simpa [labelZero] using hzero
      · simp [isLabelHOL]
    | labAsm a w bytes len =>
      simp only [labLenPosOk,lineLabLenPosOk,lineLen] at hp
      simp only [padSection]
      apply ih
      refine ⟨?_,?_,?_,?_⟩
      · simpa [List.map_cons,List.sum_cons,lineLen,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hp.2
      · simpa [List.reverse_cons,labLenPosOk_append,labLenPosOk,lineLabLenPosOk] using ha
      · simpa [labelZero] using hzero
      · simp [isLabelHOL]
    | label k1 k2 len =>
      simp only [labLenPosOk,lineLabLenPosOk,lineLen] at hp
      by_cases hz : len = 0
      · subst len
        have he : (pos + (aux.map lineLen).sum) % 2 = 0 := by
          split at hp
          · assumption
          · simp at hp
        simp only [padSection]
        apply ih
        refine ⟨?_,?_,?_,?_⟩
        · simpa [List.map_cons,List.sum_cons,lineLen] using hp.2
        · simpa [List.reverse_cons,labLenPosOk_append,labLenPosOk,lineLabLenPosOk,lineLen,List.map_reverse,List.sum_reverse,he] using ha
        · simpa [labelZero] using hzero
        · intro _
          exact labLenPosOk_evenPrefixZero _ tail ⟨he,by simpa using hp.2⟩
      · have hlen : len = 1 := by split at hp <;> omega
        have hodd : (pos + (aux.map lineLen).sum) % 2 ≠ 0 := by split at hp <;> omega
        have hn : match aux with | [] => False | x :: _ => isLabelHOL x ≠ true := by
          cases aux with
          | nil =>
            have hg := hguard True.intro
            simp [isLabelHOL,lineLen] at hg
            exact False.elim (hz hg.1)
          | cons x xs =>
            intro hx
            have hg := hguard hx
            simp [isLabelHOL,lineLen] at hg
            exact hz hg.1
        have hnall : ¬(∀ line ∈ aux, isLabelHOL line = true) := by
          cases aux with
          | nil => exact False.elim hn
          | cons x xs => exact fun h => hn (h x (by simp))
        have hs := lineLen_addNop_nonlabel nop aux hnall
        have he : (pos + ((addNop nop aux).map lineLen).sum) % 2 = 0 := by
          rw [hs]
          omega
        have had := reverseAddNop_posOk nop aux pos (by
          cases aux with
          | nil => simp at hn
          | cons x xs => exact hn) ha
        simp only [padSection,if_neg hz]
        apply ih
        refine ⟨?_,?_,?_,?_⟩
        · simpa [List.map_cons,List.sum_cons,lineLen,hs,hlen,Nat.add_assoc] using hp.2
        · simpa [List.reverse_cons,labLenPosOk_append,labLenPosOk,lineLabLenPosOk,lineLen,List.map_reverse,List.sum_reverse,he] using had
        · simpa [labelZero] using (everyLabelZero_addNop aux nop).2 hzero
        · intro _
          exact labLenPosOk_evenPrefixZero _ tail ⟨he,by simpa [hs,hlen,Nat.add_assoc] using hp.2⟩
end Flapjack.Compiler.Backend.LabToTarget
