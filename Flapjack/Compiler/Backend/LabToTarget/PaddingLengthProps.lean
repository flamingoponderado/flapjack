import Flapjack.Compiler.Backend.LabToTarget.AddNopProps
import Flapjack.Compiler.Backend.LabToTarget.PaddingLength
import Flapjack.Compiler.Backend.LabToTarget.PositionalEncoding
import Flapjack.Compiler.Backend.LabToTarget.PositionAppend
import Flapjack.Compiler.Backend.LabToTarget.PrefixZero
import Flapjack.Compiler.Backend.LabToTarget.LabelAnnotations

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Retains the original one-byte NOP, label-one and non-label accumulator guards. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_len_pad_section1"
  (words_as_type_indexed_bitvec)]
theorem lineLen_padSection_nonlabel {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (ls acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    nop.length = 1 ∧ (∀ line ∈ ls, labelOne line) ∧
      ¬(∀ line ∈ acc, isLabelHOL line = true) →
    ((padSection nop ls acc).map lineLen).sum =
      (ls.map lineLen).sum + (acc.map lineLen).sum := by
  induction ls generalizing acc with
  | nil => simp [padSection]
  | cons x xs ih =>
    rintro ⟨hnop, hls, hacc⟩
    have ht : ∀ line ∈ xs, labelOne line := fun l hm => hls l (by simp [hm])
    cases x with
    | label k1 k2 n =>
      have hn : n ≤ 1 := hls (.label k1 k2 n) (by simp)
      by_cases hz : n = 0
      · have hr := ih (.label k1 k2 0 :: acc)
          ⟨hnop, ht, by simpa [isLabelHOL] using hacc⟩
        simpa [padSection, hz, lineLen] using hr
      · have he : n = 1 := by omega
        have ha : ¬(∀ line ∈ addNop nop acc, isLabelHOL line = true) :=
          fun h => hacc ((everyIsLabel_addNop nop acc).mp h)
        have hr := ih (.label k1 k2 0 :: addNop nop acc)
          ⟨hnop, ht, by simpa [isLabelHOL] using ha⟩
        have hadd := lineLen_addNop_nonlabel nop acc hacc
        simp only [padSection, hz, ↓reduceIte, List.map_cons, List.sum_cons, lineLen] at hr ⊢
        omega
    | asm a bs n =>
      have hr := ih (.asm a (padBytes bs n nop) n :: acc)
        ⟨hnop, ht, by simp [isLabelHOL]⟩
      simp only [padSection, List.map_cons, List.sum_cons, lineLen] at hr ⊢
      omega
    | labAsm a w bs n =>
      have hr := ih (.labAsm a w (padBytes bs n nop) n :: acc)
        ⟨hnop, ht, by simp [isLabelHOL]⟩
      simp only [padSection, List.map_cons, List.sum_cons, lineLen] at hr ⊢
      omega

/-- Zero source labels suppress NOP insertion, for arbitrary NOP bytes and accumulator. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_len_pad_section0"
  (words_as_type_indexed_bitvec)]
theorem lineLen_padSection_zero {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (ls acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    (∀ line ∈ ls, labelZero line) →
    ((padSection nop ls acc).map lineLen).sum =
      (ls.map lineLen).sum + (acc.map lineLen).sum := by
  induction ls generalizing acc with
  | nil => simp [padSection]
  | cons x xs ih =>
    intro hls
    have ht : ∀ line ∈ xs, labelZero line := fun l hm => hls l (by simp [hm])
    cases x with
    | label k1 k2 n =>
      have hn : n = 0 := hls (.label k1 k2 n) (by simp)
      have hr := ih (.label k1 k2 0 :: acc) ht
      simpa [padSection, hn, lineLen] using hr
    | asm a bs n =>
      have hr := ih (.asm a (padBytes bs n nop) n :: acc) ht
      simp only [padSection, List.map_cons, List.sum_cons, lineLen] at hr ⊢
      omega
    | labAsm a w bs n =>
      have hr := ih (.labAsm a w (padBytes bs n nop) n :: acc) ht
      simp only [padSection, List.map_cons, List.sum_cons, lineLen] at hr ⊢
      omega

/-- Physical sum with all original source bounds and non-label accumulator guard. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_length_pad_section1"
  (words_as_type_indexed_bitvec)]
theorem lineLength_padSection_nonlabel {width : Nat} [NeZero width]
    (nop : List (BitVec 8))
    (ls acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    nop.length = 1 ∧ (∀ line ∈ ls, labelOne line) ∧
      (∀ line ∈ ls, lineLengthLeq line) ∧ ¬(∀ line ∈ acc, isLabelHOL line = true) ∧
      (acc.map lineLength).sum = (acc.map lineLen).sum →
    ((padSection nop ls acc).map lineLength).sum =
      (ls.map lineLen).sum + (acc.map lineLen).sum := by
  induction ls generalizing acc with
  | nil => rintro ⟨_, _, _, _, heq⟩; simpa [padSection] using heq
  | cons x xs ih =>
    rintro ⟨hnop, hls, hb, hnot, heq⟩
    have ht : ∀ line ∈ xs, labelOne line := fun l hm => hls l (by simp [hm])
    have hbt : ∀ line ∈ xs, lineLengthLeq line := fun l hm => hb l (by simp [hm])
    have hp : 0 < nop.length := by omega
    cases x with
    | label k1 k2 n =>
      have hn : n ≤ 1 := hls (.label k1 k2 n) (by simp)
      by_cases hz : n = 0
      · have hr := ih (.label k1 k2 0 :: acc)
          ⟨hnop, ht, hbt, by simpa [isLabelHOL] using hnot,
            by simpa [lineLength, lineLen] using heq⟩
        simpa [padSection, hz, lineLen] using hr
      · have he : n = 1 := by omega
        have ha : ¬(∀ line ∈ addNop nop acc, isLabelHOL line = true) :=
          fun h => hnot ((everyIsLabel_addNop nop acc).mp h)
        have haddp := lineLength_addNop_nonlabel nop acc hnot
        have hadda := lineLen_addNop_nonlabel nop acc hnot
        have hsum : ((addNop nop acc).map lineLength).sum =
            ((addNop nop acc).map lineLen).sum := by omega
        have hr := ih (.label k1 k2 0 :: addNop nop acc)
          ⟨hnop, ht, hbt, by simpa [isLabelHOL] using ha,
            by simpa [lineLength, lineLen] using hsum⟩
        simp only [padSection, hz, ↓reduceIte, List.map_cons, List.sum_cons, lineLen] at hr ⊢
        omega
    | asm a bs n =>
      have hbound : bs.length ≤ n := hb (.asm a bs n) (by simp)
      have hpad := lengthPadBytes bs nop n ⟨hp, hbound⟩
      have hr := ih (.asm a (padBytes bs n nop) n :: acc)
        ⟨hnop, ht, hbt, by simp [isLabelHOL], by simp [lineLength, lineLen, hpad, heq]⟩
      simp only [padSection, List.map_cons, List.sum_cons, lineLen] at hr ⊢
      omega
    | labAsm a w bs n =>
      have hbound : bs.length ≤ n := hb (.labAsm a w bs n) (by simp)
      have hpad := lengthPadBytes bs nop n ⟨hp, hbound⟩
      have hr := ih (.labAsm a w (padBytes bs n nop) n :: acc)
        ⟨hnop, ht, hbt, by simp [isLabelHOL], by simp [lineLength, lineLen, hpad, heq]⟩
      simp only [padSection, List.map_cons, List.sum_cons, lineLen] at hr ⊢
      omega

/-- All-label accumulator case retains the full original bounded prefix predicate. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_length_pad_section"
  (words_as_type_indexed_bitvec)]
theorem lineLength_padSection_labels {width : Nat} [NeZero width]
    (nop : List (BitVec 8))
    (ls acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    nop.length = 1 ∧ (∀ line ∈ ls, labelOne line) ∧
      (∀ line ∈ ls, lineLengthLeq line) ∧
      (acc.map lineLength).sum = (acc.map lineLen).sum ∧
      (∀ line ∈ acc, isLabelHOL line = true) ∧ labelPrefixZero ls →
    ((padSection nop ls acc).map lineLength).sum =
      (ls.map lineLen).sum + (acc.map lineLen).sum := by
  induction ls generalizing acc with
  | nil => rintro ⟨_, _, _, heq, _, _⟩; simpa [padSection] using heq
  | cons x xs ih =>
    rintro ⟨hnop, hls, hb, heq, hall, hprefix⟩
    have ht : ∀ line ∈ xs, labelOne line := fun l hm => hls l (by simp [hm])
    have hbt : ∀ line ∈ xs, lineLengthLeq line := fun l hm => hb l (by simp [hm])
    have hp : 0 < nop.length := by omega
    cases x with
    | label k1 k2 n =>
      have hpr : n = 0 ∧ labelPrefixZero xs := by
        simpa [labelPrefixZero_cons_iff, isLabelHOL, lineLen] using hprefix
      have hr := ih (.label k1 k2 0 :: acc)
        ⟨hnop, ht, hbt, by simpa [lineLength, lineLen] using heq,
          by simpa [isLabelHOL] using hall, hpr.2⟩
      simpa [padSection, hpr.1, lineLen] using hr
    | asm a bs n =>
      have hbound : bs.length ≤ n := hb (.asm a bs n) (by simp)
      have hpad := lengthPadBytes bs nop n ⟨hp, hbound⟩
      have hr := lineLength_padSection_nonlabel nop xs (.asm a (padBytes bs n nop) n :: acc)
        ⟨hnop, ht, hbt, by simp [isLabelHOL], by simp [lineLength, lineLen, hpad, heq]⟩
      simp only [padSection, List.map_cons, List.sum_cons, lineLen] at hr ⊢
      omega
    | labAsm a w bs n =>
      have hbound : bs.length ≤ n := hb (.labAsm a w bs n) (by simp)
      have hpad := lengthPadBytes bs nop n ⟨hp, hbound⟩
      have hr := lineLength_padSection_nonlabel nop xs (.labAsm a w (padBytes bs n nop) n :: acc)
        ⟨hnop, ht, hbt, by simp [isLabelHOL], by simp [lineLength, lineLen, hpad, heq]⟩
      simp only [padSection, List.map_cons, List.sum_cons, lineLen] at hr ⊢
      omega

/-- Preserves the original map equality, not merely equality of its sum. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "label_zero_line_length_pad_section"
  (words_as_type_indexed_bitvec)]
theorem lineLength_padSection_zero {width : Nat} [NeZero width]
    (nop : List (BitVec 8))
    (ls acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    0 < nop.length ∧ (∀ line ∈ ls, labelZero line) ∧
      acc.map lineLength = acc.map lineLen ∧ (∀ line ∈ ls, lineLengthLeq line) →
    (padSection nop ls acc).map lineLength = (acc.reverse ++ ls).map lineLen := by
  induction ls generalizing acc with
  | nil =>
    rintro ⟨_, _, heq, _⟩
    simpa [padSection, List.map_reverse] using congrArg List.reverse heq
  | cons x xs ih =>
    rintro ⟨hnop, hls, heq, hb⟩
    have ht : ∀ line ∈ xs, labelZero line := fun l hm => hls l (by simp [hm])
    have hbt : ∀ line ∈ xs, lineLengthLeq line := fun l hm => hb l (by simp [hm])
    cases x with
    | label k1 k2 n =>
      have hn : n = 0 := hls (.label k1 k2 n) (by simp)
      have ha : (List.map lineLength (.label k1 k2 0 :: acc)) =
          List.map lineLen (.label k1 k2 0 :: acc) := by simp [lineLength, lineLen, heq]
      have hr := ih (.label k1 k2 0 :: acc) ⟨hnop, ht, ha, hbt⟩
      simpa [padSection, hn, List.reverse_cons, List.append_assoc] using hr
    | asm a bs n =>
      have hbound : bs.length ≤ n := hb (.asm a bs n) (by simp)
      have hp := lengthPadBytes bs nop n ⟨hnop, hbound⟩
      have ha : (List.map lineLength (.asm a (padBytes bs n nop) n :: acc)) =
          List.map lineLen (.asm a (padBytes bs n nop) n :: acc) := by
        simp [lineLength, lineLen, hp, heq]
      have hr := ih (.asm a (padBytes bs n nop) n :: acc) ⟨hnop, ht, ha, hbt⟩
      simpa [padSection, List.reverse_cons, List.append_assoc, List.map_append, lineLen] using hr
    | labAsm a w bs n =>
      have hbound : bs.length ≤ n := hb (.labAsm a w bs n) (by simp)
      have hp := lengthPadBytes bs nop n ⟨hnop, hbound⟩
      have ha : (List.map lineLength (.labAsm a w (padBytes bs n nop) n :: acc)) =
          List.map lineLen (.labAsm a w (padBytes bs n nop) n :: acc) := by
        simp [lineLength, lineLen, hp, heq]
      have hr := ih (.labAsm a w (padBytes bs n nop) n :: acc) ⟨hnop, ht, ha, hbt⟩
      simpa [padSection, List.reverse_cons, List.append_assoc, List.map_append, lineLen] using hr

end Flapjack.Compiler.Backend.LabToTarget
