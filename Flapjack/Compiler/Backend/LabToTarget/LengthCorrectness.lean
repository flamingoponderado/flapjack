import Flapjack.Compiler.Backend.LabToTarget.RemoveLabels
import Flapjack.Compiler.Backend.LabToTarget.LineLength
import Flapjack.Compiler.Backend.LabProps.LineLength
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_length_ok_def"
  (words_as_type_indexed_bitvec)]
def lineLengthOk {width : Nat} [NeZero width] (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) : Prop :=
  (lineBytes line).length = lineLen line

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_length_ok_def"
  (words_as_type_indexed_bitvec)]
def secLengthOk {width : Nat} [NeZero width] (sec : Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) : Prop :=
  ∀ line ∈ sec.lines, lineLengthOk line

/-- Retains the original EVERY guard and arbitrary starting position. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_length_sum_line_length"
  (words_as_type_indexed_bitvec)]
theorem secLength_sumLineLength {width : Nat} [NeZero width]
    (ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (n : Nat) :
    (∀ line ∈ ls, lineLengthOk line) → secLength ls n = (ls.map lineLength).sum + n := by
  induction ls generalizing n with
  | nil => simp [secLength]
  | cons line rest ih =>
    intro h
    have hx := h line (by simp)
    have ht : ∀ l ∈ rest, lineLengthOk l := fun l hm => h l (by simp [hm])
    cases line with
    | label k1 k2 len =>
      have hz : len = 0 := by simpa [lineLengthOk, lineBytes, lineLen] using hx.symm
      simpa [secLength, lineLength, hz] using ih n ht
    | asm a bs len =>
      have he : bs.length = len := hx
      have hr := ih (n + len) ht
      simp only [secLength, List.map_cons, List.sum_cons, lineLength]
      omega
    | labAsm a w bs len =>
      have he : bs.length = len := hx
      have hr := ih (n + len) ht
      simp only [secLength, List.map_cons, List.sum_cons, lineLength]
      omega
end Flapjack.Compiler.Backend.LabToTarget
