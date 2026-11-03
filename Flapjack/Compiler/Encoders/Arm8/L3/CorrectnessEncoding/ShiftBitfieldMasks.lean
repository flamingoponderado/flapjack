import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.ShiftBitfield

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

/-!
# Mask algebra for the `BitfieldMove@64` shift-immediate forms

`DecodeBitMasks` at the shapes `arm8_ast` emits for `Shift` with an immediate,
together with the mask identities of `arm8_targetProofScript.sml`'s `lsl`,
`lsr` and `asr2`.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- `DecodeBitMasks` at the `Lsr`/`Asr` shape `(1, 63w, n2w n, F)`; the two
masks are the all-ones word and the "keep the low `64 - n` bits" word. -/
theorem decodeBitMasks_lsr (n : Nat) (hn : n < 64) :
    DecodeBitMasks (TM := 64)
      ((1 : BitVec 1), (BitVec.ofNat 6 63, (BitVec.ofNat 6 n, false))) =
      some (Replicate (holRotate (holPadLeft false 64 (Ones 64)) n),
        Replicate (holPadLeft false 64 (Ones (63 - n + 1)))) := by
  interval_cases n <;> decide

/-- The `Lsr`/`Asr` tmask word keeps exactly the low `64 - n` bits. -/
theorem tmask_lsr_getLsbD (n i : Nat) (hn : n < 64) (hi : i < 64) :
    (Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - n + 1)))).getLsbD i =
      decide (i < 64 - n) := by
  have hsub : 63 - n + 1 = 64 - n := by omega
  rw [hsub]
  have hlen : (holPadLeft false 64 (Ones (64 - n))).length = 64 := by
    simp [holPadLeft, Ones, List.length_replicate]
  have hrep : holReplicate (holPadLeft false 64 (Ones (64 - n))) 1 =
      holPadLeft false 64 (Ones (64 - n)) := by
    simp [holReplicate]
  have hgetD : (holPadLeft false 64 (Ones (64 - n))).getD (63 - i) false =
      decide (n ≤ 63 - i) := by
    have hOnes : Ones (64 - n) = List.replicate (64 - n) true := by
      simp [Ones, holPadLeft]
    rw [hOnes, holPadLeft, List.length_replicate]
    have hn64 : 64 - (64 - n) = n := by omega
    rw [hn64]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append, List.length_replicate]
    by_cases h : 63 - i < n
    · rw [if_pos h]
      simp [h]
    · rw [if_neg h]
      have h2 : 63 - i - n < 64 - n := by omega
      rw [List.getElem?_replicate]
      simp [h2]
      omega
  simp only [Replicate, hlen, Nat.reduceDiv, hrep, Flapjack.RiscV.L3.holV2w,
    Flapjack.getLsbD_holFcpWord, hgetD, hi, decide_true, Bool.true_and]
  have hiff : (n ≤ 63 - i) ↔ (i < 64 - n) := by omega
  simp [hiff]

end Flapjack.Compiler.Encoders.Arm8.L3
