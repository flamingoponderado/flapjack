import Flapjack.RiscV.Backend
import Flapjack.RiscV.Lab

namespace Flapjack.RiscV

/-! The checked Word boundary is definitionally the same AUIPC/ADDI pair as
the layout-aware Lab lowering.  Keep this bridge in the production API so
correctness clients do not need to restate the encoder equation in tests. -/

/-! The public standalone Word boundary is now the position-zero instance of
the Cake-faithful `AUIPC`/`ADDI` lowering.  The explicit state argument in the
agreement theorems below remains useful to callers, but no longer hides a
truncating single-instruction model. -/

theorem uImmediate_zero [NeZero width] : uImmediate (0 : Word width) = 0 := by
  unfold uImmediate
  ext i
  simp [BitVec.getElem_signExtend]

/-! ## Cake-faithful LocValue execution oracles (bead flapjack-pxn.1.4)

    The checked lowering `wordLocValueToInstructionsCake destination label position`
    mirrors Cake's PC-relative `Loc` encoding: it emits `AUIPC`/`ADDI` for the
    offset `label - position`.  Executing that pair from `pc = position` therefore
    yields `label`.  These `by decide` oracles exercise the out-of-range and
    page-crossing shapes that the legacy one-instruction boundary truncates. -/

theorem locValue_balanced_reconstruction (delta : Int) :
    (let remainder := delta % 4096
     let low := if remainder >= 2048 then remainder - 4096 else remainder
     let upper := (delta - low) / 4096
     low + upper * 4096) = delta := by
  dsimp only
  split <;> omega

/-! ### Range boundary of the `AUIPC` immediate (bead flapjack-pxn.1.4)

    The generic execution identity for `wordLocValueToInstructionsCake` needs the
    pc-relative delta to fit the signed 32-bit `AUIPC`+`ADDI` range; equivalently
    the `upper` word must fit signed 20 bits.  Outside that range the `AUIPC`
    immediate sign-wraps, exactly as in Cake's `riscv_ast`.  The first
    out-of-range `upper`, `2 ^ 19`, is a concrete counterexample to the naive
    unconditional identity, while in-range values satisfy it. -/

example :
    uImmediate (BitVec.ofInt 64 (2 ^ 19 : Int)) ≠
      BitVec.ofInt 64 ((2 ^ 19 : Int) * 4096) := by decide

example :
    uImmediate (BitVec.ofInt 64 (1 : Int)) =
      BitVec.ofInt 64 ((1 : Int) * 4096) := by decide

example :
    uImmediate (BitVec.ofInt 64 (-1 : Int)) =
      BitVec.ofInt 64 ((-1 : Int) * 4096) := by decide

/-! ### Kernel-checked reconstruction for nonnegative (forward) offsets

The reconstruction premise used by `wordLocValueToInstructionsCake_execution_of_reconstruction`
is discharged here for the nonnegative-offset range, i.e. forward references where the
target is at or after the current position. The signed range needs the negative case as
well and remains an explicit obligation. (bead flapjack-pxn.1.4) -/

theorem bmod_ofInt_toNat_nonneg (upper : Int) (h0 : 0 ≤ upper) (hhi : upper < 2^19) :
    (((BitVec.ofInt 64 upper).toNat : Int)).bmod (2^20) = upper := by
  rw [BitVec.toNat_ofInt]
  have h1 : upper % ((2^64 : Nat) : Int) = upper := Int.emod_eq_of_lt h0 (by omega)
  rw [h1, Int.toNat_of_nonneg h0]
  have hb1 : -(↑(2^20 : Nat) / 2) ≤ upper := by omega
  have hb2 : upper < (↑(2^20 : Nat) + 1) / 2 := by omega
  exact Int.bmod_eq_of_le (n := upper) (m := (2:Nat)^20) hb1 hb2

theorem signExtend_ofNat_ofInt_nonneg (upper : Int) (h0 : 0 ≤ upper) (hhi : upper < 2^19) :
    BitVec.signExtend 64 (BitVec.ofNat 20 (BitVec.ofInt 64 upper).toNat) =
      BitVec.ofInt 64 upper := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend]
  change ((OfNat.ofNat ((BitVec.ofInt 64 upper).toNat) : BitVec 20).toInt).bmod
      (2 ^ min 64 20) = (BitVec.ofInt 64 upper).toInt
  rw [BitVec.toInt_ofNat, BitVec.toInt_ofInt, Nat.min_eq_right (by omega : 20 ≤ 64)]
  rw [bmod_ofInt_toNat_nonneg upper h0 hhi]
  have hb1 : -(↑(2^20 : Nat) / 2) ≤ upper := by omega
  have hb2 : upper < (↑(2^20 : Nat) + 1) / 2 := by omega
  rw [Int.bmod_eq_of_le (n := upper) (m := (2:Nat)^20) hb1 hb2]
  have hc1 : -(↑(2^64 : Nat) / 2) ≤ upper := by omega
  have hc2 : upper < (↑(2^64 : Nat) + 1) / 2 := by omega
  exact (Int.bmod_eq_of_le (n := upper) (m := (2:Nat)^64) hc1 hc2).symm

theorem uImmediate_ofInt_range_nonneg (upper : Int) (h0 : 0 ≤ upper) (hhi : upper < 2^19) :
    uImmediate (BitVec.ofInt 64 upper) = BitVec.ofInt 64 (upper * 4096) := by
  rw [uImmediate, signExtend_ofNat_ofInt_nonneg upper h0 hhi]
  rw [BitVec.shiftLeft_eq, BitVec.shiftLeft_eq_mul_twoPow, BitVec.ofInt_mul]
  rw [show BitVec.twoPow 64 12 = BitVec.ofInt 64 4096 by decide]

/-! ### Kernel-checked reconstruction for the full signed offset range

The negative-offset (backward reference) case of the reconstruction, so the
premise of `wordLocValueToInstructionsCake_execution_of_reconstruction` is
discharged for every signed 20-bit `upper`, i.e. every `delta = label - position`
with `-(2^19) ≤ delta < 2^19`. (bead flapjack-pxn.1.4) -/

theorem bmod_ofInt_toNat_neg (upper : Int) (hlo : -(2^19) ≤ upper) (hneg : upper < 0) :
    (((BitVec.ofInt 64 upper).toNat : Int)).bmod (2^20) = upper := by
  rw [BitVec.toNat_ofInt]
  have hmod : upper % ((2^64 : Nat) : Int) = upper + ((2^64 : Nat) : Int) := by
    have h2 : upper % ((2^64 : Nat) : Int) =
        (upper + ((2^64 : Nat) : Int)) % ((2^64 : Nat) : Int) := by
      apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
      have hsub : upper - (upper + ((2^64 : Nat) : Int)) = -(((2^64 : Nat) : Int)) := by
        omega
      rw [hsub]; decide
    rw [h2]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  rw [hmod]
  rw [Int.toNat_of_nonneg (by omega : (0:Int) ≤ upper + ((2^64 : Nat) : Int))]
  rw [Int.bmod_eq_emod]
  have hper : (upper + ((2^64 : Nat) : Int)) % ((2^20 : Nat) : Int) =
      upper + ((2^20 : Nat) : Int) := by
    rw [Int.add_emod]
    have hz : ((2^64 : Nat) : Int) % ((2^20 : Nat) : Int) = 0 := by decide
    rw [hz]
    have hu : upper % ((2^20 : Nat) : Int) = upper + ((2^20 : Nat) : Int) := by
      have h2 : upper % ((2^20 : Nat) : Int) =
          (upper + ((2^20 : Nat) : Int)) % ((2^20 : Nat) : Int) := by
        apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
        have hsub : upper - (upper + ((2^20 : Nat) : Int)) = -(((2^20 : Nat) : Int)) := by
          omega
        rw [hsub]; decide
      rw [h2]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [hu]
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  rw [hper]
  have hc : (((2^20 : Nat) : Int) + 1) / 2 = 524288 := by decide
  rw [if_pos (by rw [hc]; omega :
    (((2^20 : Nat) : Int) + 1) / 2 ≤ upper + ((2^20 : Nat) : Int))]
  omega

theorem bmod_ofInt_toNat_range (upper : Int) (hlo : -(2^19) ≤ upper) (hhi : upper < 2^19) :
    (((BitVec.ofInt 64 upper).toNat : Int)).bmod (2^20) = upper := by
  by_cases h : 0 ≤ upper
  · exact bmod_ofInt_toNat_nonneg upper h hhi
  · exact bmod_ofInt_toNat_neg upper hlo (by omega)

theorem signExtend_ofNat_ofInt_range (upper : Int) (hlo : -(2^19) ≤ upper)
    (hhi : upper < 2^19) :
    BitVec.signExtend 64 (BitVec.ofNat 20 (BitVec.ofInt 64 upper).toNat) =
      BitVec.ofInt 64 upper := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend]
  change ((OfNat.ofNat ((BitVec.ofInt 64 upper).toNat) : BitVec 20).toInt).bmod
      (2 ^ min 64 20) = (BitVec.ofInt 64 upper).toInt
  rw [BitVec.toInt_ofNat, BitVec.toInt_ofInt, Nat.min_eq_right (by omega : 20 ≤ 64)]
  rw [bmod_ofInt_toNat_range upper hlo hhi]
  have hb1 : -(↑(2^20 : Nat) / 2) ≤ upper := by omega
  have hb2 : upper < (↑(2^20 : Nat) + 1) / 2 := by omega
  rw [Int.bmod_eq_of_le (n := upper) (m := (2:Nat)^20) hb1 hb2]
  have hc1 : -(↑(2^64 : Nat) / 2) ≤ upper := by omega
  have hc2 : upper < (↑(2^64 : Nat) + 1) / 2 := by omega
  exact (Int.bmod_eq_of_le (n := upper) (m := (2:Nat)^64) hc1 hc2).symm

theorem uImmediate_ofInt_range (upper : Int) (hlo : -(2^19) ≤ upper) (hhi : upper < 2^19) :
    uImmediate (BitVec.ofInt 64 upper) = BitVec.ofInt 64 (upper * 4096) := by
  rw [uImmediate, signExtend_ofNat_ofInt_range upper hlo hhi]
  rw [BitVec.shiftLeft_eq, BitVec.shiftLeft_eq_mul_twoPow, BitVec.ofInt_mul]
  rw [show BitVec.twoPow 64 12 = BitVec.ofInt 64 4096 by decide]

/-- The AUIPC immediate reconstruction, phrased for a balanced `low`/`upper`
split of a signed offset `delta` rather than for `uImmediate`'s own expression:
if `low` is in `[-2048, 2048)` and `low + upper * 4096 = delta` with
`|delta| < 2^19`, then `uImmediate (ofInt 64 upper)` is exactly
`ofInt 64 (upper * 4096)`. (bead flapjack-pxn.1.4) -/
theorem uImmediate_ofInt_balanced (delta upper low : Int)
    (hlo : -(2^19) ≤ delta) (hhi : delta < 2^19)
    (hlow_lo : -2048 ≤ low) (hlow_hi : low ≤ 2047)
    (hbal : low + upper * 4096 = delta) :
    uImmediate (BitVec.ofInt 64 upper) = BitVec.ofInt 64 (upper * 4096) := by
  have hupper_lo : -(2^19) ≤ upper := by omega
  have hupper_hi : upper < 2^19 := by omega
  exact uImmediate_ofInt_range upper hupper_lo hupper_hi

/-- The balanced LocValue reconstruction in the `upper * 4096 + low` order,
which is the orientation produced by `BitVec.ofInt_add`. (bead flapjack-pxn.1.4) -/
theorem locValue_balanced_reconstruction_comm (delta : Int) :
    (delta - (if delta % 4096 ≥ 2048 then delta % 4096 - 4096 else delta % 4096)) / 4096 * 4096 +
      (if delta % 4096 ≥ 2048 then delta % 4096 - 4096 else delta % 4096) = delta := by
  have hbal := locValue_balanced_reconstruction delta
  dsimp only at hbal
  omega

end Flapjack.RiscV
