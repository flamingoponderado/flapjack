module

public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.ShiftBitfield
public import Flapjack.HolRef

@[expose] public section

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

/-- The `Lsr`/`Asr` wmask is the all-ones word: rotating the all-ones word
leaves it unchanged. -/
theorem wmask_lsr (n : Nat) (hn : n < 64) :
    Replicate (TN := 64) (holRotate (holPadLeft false 64 (Ones 64)) n) =
      BitVec.allOnes 64 := by
  interval_cases n <;> decide

/-- `arm8_targetProofScript.sml`'s `lsr`: masking the rotate right by the
`Lsr` masks is the logical shift right. -/
theorem lsr_mask (x : BitVec 64) (n : Nat) (hn : n < 64) :
    ((x.rotateRight n &&& Replicate (TN := 64) (holRotate (holPadLeft false 64 (Ones 64)) n)) &&&
      Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - n + 1)))) = x >>> n := by
  rw [wmask_lsr n hn, BitVec.and_allOnes]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_rotateRight, BitVec.getLsbD_ushiftRight,
    tmask_lsr_getLsbD n i hn hi, Nat.mod_eq_of_lt hn]
  by_cases h : i < 64 - n
  · simp [h]
  · simp [h]
    have hge : 64 ≤ n + i := by omega
    have hfalse : x.getLsbD (n + i) = false := by
      simp only [BitVec.getLsbD]
      rw [Nat.testBit_lt_two_pow]
      calc x.toNat < 2 ^ 64 := x.isLt
        _ ≤ 2 ^ (n + i) := Nat.pow_le_pow_right (by norm_num) hge
    rw [hfalse]

/-- `Replicate` of a one-bit list has that bit at every position. -/
theorem replicate_true_eq : Replicate (TN := 64) [true] = BitVec.allOnes 64 := by decide

theorem replicate_false_eq : Replicate (TN := 64) [false] = (0 : BitVec 64) := by decide

theorem replicate_single_getLsbD (b : Bool) (i : Nat) (hi : i < 64) :
    (Replicate (TN := 64) [b]).getLsbD i = b := by
  cases b
  · rw [replicate_false_eq]; simp
  · rw [replicate_true_eq]
    exact BitVec.getElem_allOnes i hi

/-- `arm8_targetProofScript.sml`'s `asr2`: the sign-extended rotate right by
the `Asr` masks is the arithmetic shift right. -/
theorem asr_mask (x : BitVec 64) (n : Nat) (hn : n < 64) :
    ((Replicate (TN := 64) [x.getLsbD 63] &&&
        ~~~(Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - n + 1))))) |||
      ((x.rotateRight n &&& Replicate (TN := 64) (holRotate (holPadLeft false 64 (Ones 64)) n)) &&&
        Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - n + 1))))) = x.sshiftRight n := by
  have hmsb : x.msb = x.getLsbD 63 := by
    simp [BitVec.msb, BitVec.getMsbD, BitVec.getLsbD]
  rw [wmask_lsr n hn, BitVec.and_allOnes]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_and,
    BitVec.getLsbD_rotateRight, BitVec.getLsbD_sshiftRight, tmask_lsr_getLsbD n i hn hi,
    Nat.mod_eq_of_lt hn, hmsb, replicate_single_getLsbD _ i hi]
  by_cases h : i < 64 - n
  · have hni : n + i < 64 := by omega
    simp [h, hi, hni]
  · have hge : 64 ≤ n + i := by omega
    have hni : ¬ n + i < 64 := by omega
    have h64 : ¬ 64 ≤ i := by omega
    simp [h, hge, hni, h64, hi]

/-- The `Lsl` wmask: bits `n` through 63 set. -/
def arm8LslMask (n : Nat) : BitVec 64 :=
  holV2w 64 (List.replicate (64 - n) true ++ List.replicate n false)

/-- `DecodeBitMasks` at the `Lsl` shape `(1, 63w - n2w n, -n2w n, F)`: the
wmask keeps the bits above `n` and the tmask is all ones. -/
theorem decodeBitMasks_lsl (n : Nat) (hn : n < 64) :
    DecodeBitMasks (TM := 64)
      ((1 : BitVec 1), (BitVec.ofNat 6 ((63 - n) % 64), (BitVec.ofNat 6 ((64 - n) % 64), false))) =
      some (Replicate (TN := 64)
          (holRotate (holPadLeft false 64 (Ones ((63 - n) % 64 + 1))) ((64 - n) % 64)),
        BitVec.allOnes 64) := by
  interval_cases n <;> decide

/-- The rendered `Lsl` wmask is `arm8LslMask`. -/
theorem wmask_lsl_eq (n : Nat) (hn : n < 64) :
    Replicate (TN := 64)
        (holRotate (holPadLeft false 64 (Ones ((63 - n) % 64 + 1))) ((64 - n) % 64)) =
      arm8LslMask n := by
  interval_cases n <;> decide

/-- `arm8LslMask` keeps exactly the bits at positions `n` and above. -/
theorem arm8LslMask_getLsbD (n i : Nat) (hn : n < 64) (hi : i < 64) :
    (arm8LslMask n).getLsbD i = decide (n ≤ i) := by
  have hlen : (List.replicate (64 - n) true ++ List.replicate n false).length = 64 := by
    simp [List.length_replicate]
    omega
  have h63 : 63 - i < 64 := by omega
  simp only [arm8LslMask, Flapjack.RiscV.L3.holV2w, Flapjack.getLsbD_holFcpWord, hlen, hi,
    decide_true, Bool.true_and]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append, List.length_replicate]
  by_cases h : 63 - i < 64 - n
  · rw [if_pos h]
    simp [h]
    omega
  · rw [if_neg h]
    have h2 : 63 - i - (64 - n) < n := by omega
    rw [List.getElem?_replicate]
    simp [h2]
    omega

/-- `arm8_targetProofScript.sml`'s `lsl`: masking the rotate right by the
`Lsl` masks is the logical shift left. -/
theorem lsl_mask (x : BitVec 64) (n : Nat) (hn : n < 64) :
    ((BitVec.allOnes 64 &&&
        Replicate (TN := 64)
          (holRotate (holPadLeft false 64 (Ones ((63 - n) % 64 + 1))) ((64 - n) % 64))) &&&
      x.rotateRight ((64 - n) % 64)) = x <<< n := by
  rw [wmask_lsl_eq n hn, BitVec.allOnes_and]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_rotateRight, BitVec.getLsbD_shiftLeft,
    arm8LslMask_getLsbD n i hn hi]
  by_cases hn0 : n = 0
  · subst hn0
    simp [hi]
  · have hmod : (64 - n) % 64 = 64 - n := by
      rw [Nat.mod_eq_of_lt]; omega
    rw [hmod]
    have hn64 : 64 - (64 - n) = n := by omega
    by_cases h : n ≤ i
    · have hlt : ¬ i < n := by omega
      simp [hmod, hn64, hlt]
      omega
    · have hlt : i < n := by omega
      simp [hmod, hn64, hlt]

/-- HOL `lsr`: masking the rotate right by the `DecodeBitMasks` masks is the
logical shift right. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "lsr"]
theorem arm8LsrMaskIdentity (n : Nat) (x wmask tmask : BitVec 64) (hn : n < 64)
    (hmasks : DecodeBitMasks (TM := 64)
      ((1 : BitVec 1), (BitVec.ofNat 6 63, (BitVec.ofNat 6 n, false))) = some (wmask, tmask)) :
    ((tmask &&& wmask) &&& x.rotateRight n) = x >>> n := by
  rw [decodeBitMasks_lsr n hn] at hmasks
  have hp := Option.some.inj hmasks
  rw [← (Prod.mk.inj hp).1, ← (Prod.mk.inj hp).2]
  calc (Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - n + 1))) &&&
        Replicate (TN := 64) (holRotate (holPadLeft false 64 (Ones 64)) n)) &&& x.rotateRight n
      = x.rotateRight n &&&
        (Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - n + 1))) &&&
          Replicate (TN := 64) (holRotate (holPadLeft false 64 (Ones 64)) n)) :=
        BitVec.and_comm _ _
    _ = x.rotateRight n &&&
        (Replicate (TN := 64) (holRotate (holPadLeft false 64 (Ones 64)) n) &&&
          Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - n + 1)))) := by
        rw [BitVec.and_comm (Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - n + 1))))]
    _ = (x.rotateRight n &&& Replicate (TN := 64) (holRotate (holPadLeft false 64 (Ones 64)) n)) &&&
          Replicate (TN := 64) (holPadLeft false 64 (Ones (63 - n + 1))) :=
        (BitVec.and_assoc _ _ _).symm
    _ = x >>> n := lsr_mask x n hn

/-- HOL `lsl`: masking the rotate right by the `DecodeBitMasks` masks at
`(1, q, r, F)` with `r = -n` and `q = r + 63w` is the logical shift left. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "lsl"]
theorem arm8LslMaskIdentity (n : Nat) (x wmask tmask : BitVec 64) (r q : BitVec 6)
    (hn : n < 64)
    (hr : r = BitVec.ofNat 6 ((64 - n) % 64))
    (hq : q = r + BitVec.ofNat 6 63)
    (hmasks : DecodeBitMasks (TM := 64) ((1 : BitVec 1), (q, (r, false))) = some (wmask, tmask)) :
    ((tmask &&& wmask) &&& x.rotateRight r.toNat) = x <<< n := by
  have hq' : q = BitVec.ofNat 6 ((63 - n) % 64) := by
    rw [hq, hr]
    interval_cases n <;> decide
  have hrt : r.toNat = (64 - n) % 64 := by rw [hr, BitVec.toNat_ofNat]; norm_num
  rw [hq', hr] at hmasks
  rw [decodeBitMasks_lsl n hn] at hmasks
  have hp := Option.some.inj hmasks
  rw [← (Prod.mk.inj hp).1, ← (Prod.mk.inj hp).2, hrt]
  exact lsl_mask x n hn

end Flapjack.Compiler.Encoders.Arm8.L3
