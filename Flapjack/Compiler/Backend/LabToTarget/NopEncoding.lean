import Flapjack.Compiler.Encoders.Asm
import Flapjack.HolRef
import Mathlib.Data.List.Flatten

/-! Original NOP-padding relation used by assembly-step refinement.
The source leaves encoded-list elements generic; only the assembly instruction
word dimension translates to positive-width BitVec through native HolAsm. -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "enc_with_nop_def" (words_as_type_indexed_bitvec)]
def encWithNop {width : Nat} [NeZero width] {Value : Type}
    (encode : HolAsm width → List Value) (instruction : HolAsm width)
    (bytes : List Value) : Prop :=
  let initial := encode instruction
  let step := encode (.inst .skip)
  if step.length = 0 then bytes = initial
  else let count := (bytes.length - initial.length) / step.length
       bytes = initial ++ (List.replicate count step).flatten

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "enc_with_nop_thm" (words_as_type_indexed_bitvec)]
theorem encWithNop_iff {width : Nat} [NeZero width] {Value : Type}
    (encode : HolAsm width → List Value) (instruction : HolAsm width)
    (bytes : List Value) :
    encWithNop encode instruction bytes ↔
      ∃ count, bytes = encode instruction ++
        (List.replicate count (encode (.inst .skip))).flatten := by
  unfold encWithNop
  dsimp only
  by_cases hzero : (encode (.inst .skip)).length = 0
  · have hnil : encode (.inst .skip) = [] := List.length_eq_zero_iff.mp hzero
    simp [hnil]
  · simp only [hzero, ↓reduceIte]
    constructor
    · intro h
      exact ⟨_, h⟩
    · rintro ⟨count, rfl⟩
      have hlength : (List.replicate count (encode (.inst .skip))).flatten.length =
          count * (encode (.inst .skip)).length := by
        induction count with
        | zero => simp
        | succ count ih => simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]
      simp only [List.length_append, hlength, Nat.add_sub_cancel_left]
      rw [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hzero)]

end Flapjack.Compiler.Backend.LabToTarget
