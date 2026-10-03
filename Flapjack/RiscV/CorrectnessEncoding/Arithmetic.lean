import Flapjack.HolRef
import Flapjack.Misc.Alignment
import Flapjack.RiscV.L3.Support

/-! Fixed-width arithmetic prerequisites from `riscv_targetProofScript.sml`.
The original `lem5` and `lem8` use free word/Boolean variables, bound explicitly
here; `lem9` and `mul_long` quantify both word64 operands. `ror` retains its
original natural shift amount and sole strict bound. No target-state or
execution hypothesis is added. -/
namespace Flapjack.RiscV.TargetProof
open Flapjack.RiscV.L3

@[hol "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml" "lem5"]
theorem aligned_bit_one (c : BitVec 64) (h : Flapjack.holAligned 2 c = true) :
    c.getLsbD 1 = false := by
  have eq : Flapjack.holAlign 2 c = c := of_decide_eq_true h
  have bit := congrArg (fun w : BitVec 64 => w.getLsbD 1) eq
  simp only [Flapjack.holAlign, Flapjack.holWordSlice] at bit
  rw [Flapjack.getLsbD_holFcpWord] at bit
  simpa using bit.symm

@[hol "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml" "lem8"]
theorem singleton_or (b x y : Bool) :
    ((if b then (1 : BitVec 64) else 0) = (holV2w 64 [x] ||| holV2w 64 [y])) ↔
      b = (x || y) := by
  set_option maxRecDepth 4096 in
    cases b <;> cases x <;> cases y <;> decide

@[hol "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml" "lem9"]
theorem carry_widen (r2 r3 : BitVec 64) :
    (18446744073709551616 ≤ r2.toNat + (r3.toNat + 1) ↔
      (18446744073709551616 : BitVec 65).ule
        (r2.setWidth 65 + r3.setWidth 65 + 1) = true) ∧
    (18446744073709551616 ≤ r2.toNat + r3.toNat ↔
      (18446744073709551616 : BitVec 65).ule
        (r2.setWidth 65 + r3.setWidth 65) = true) := by
  have h2 := r2.isLt
  have h3 := r3.isLt
  have e2 := BitVec.toNat_setWidth_of_le (b := r2) (w' := 65) (by decide)
  have e3 := BitVec.toNat_setWidth_of_le (b := r3) (w' := 65) (by decide)
  simp only [BitVec.ule_eq_decide, BitVec.toNat_add, e2, e3, decide_eq_true_eq]
  change r2.toNat < 18446744073709551616 at h2
  change r3.toNat < 18446744073709551616 at h3
  change (18446744073709551616 ≤ r2.toNat + (r3.toNat + 1) ↔
    18446744073709551616 ≤ ((r2.toNat + r3.toNat) % 36893488147419103232 + 1) % 36893488147419103232) ∧
    (18446744073709551616 ≤ r2.toNat + r3.toNat ↔
    18446744073709551616 ≤ (r2.toNat + r3.toNat) % 36893488147419103232)
  omega

@[hol "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml" "mul_long"]
theorem mul_long (a b : BitVec 64) :
    BitVec.ofNat 64 ((a.toNat * b.toNat) / 18446744073709551616) =
      BitVec.extractLsb' 64 64 (a.setWidth 128 * b.setWidth 128) := by
  have bound : a.toNat * b.toNat < 2 ^ 128 :=
    BitVec.toNat_mul_toNat_lt
  have ea := BitVec.toNat_setWidth_of_le (b := a) (w' := 128) (by decide)
  have eb := BitVec.toNat_setWidth_of_le (b := b) (w' := 128) (by decide)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, BitVec.toNat_mul,
    ea, eb, Nat.mod_eq_of_lt bound, Nat.shiftRight_eq_div_pow]

@[hol "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml" "ror"]
theorem ror (w : BitVec 64) (n : Nat) (h : n < 64) :
    ((w <<< (64 - n)) ||| (w >>> n)) = w.rotateRight n := by
  rw [BitVec.rotateRight_eq_rotateRightAux_of_lt h]
  exact BitVec.or_comm _ _

end Flapjack.RiscV.TargetProof
