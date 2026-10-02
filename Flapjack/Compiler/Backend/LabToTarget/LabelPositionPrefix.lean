import Flapjack.Compiler.Backend.LabToTarget.LabelPosition
import Flapjack.Compiler.Backend.LabToTarget.PrefixZero
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Full original even-position and label-parity implication. Nonlabel fields
are unrestricted; the bounded prefix predicate observes only initial labels. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lab_len_pos_ok_even_prefix_zero"
  (words_as_type_indexed_bitvec)]
theorem labLenPosOk_evenPrefixZero {width : Nat} [NeZero width] (pos : Nat)
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    pos % 2 = 0 ∧ labLenPosOk pos lines → labelPrefixZero lines := by
  induction lines generalizing pos with
  | nil => simp
  | cons line tail ih =>
    rintro ⟨he,hpos⟩
    cases line with
    | label k1 k2 len =>
      simp only [labLenPosOk,lineLabLenPosOk,he,if_pos,lineLen] at hpos
      rcases hpos with ⟨hlen,ht⟩
      subst len
      simp only [Nat.add_zero] at ht
      exact (labelPrefixZero_cons_iff _ _).2 (fun _ => ⟨rfl,ih pos ⟨he,ht⟩⟩)
    | asm a bytes len => simp [isLabelHOL]
    | labAsm a w bytes len => simp [isLabelHOL]
end Flapjack.Compiler.Backend.LabToTarget
