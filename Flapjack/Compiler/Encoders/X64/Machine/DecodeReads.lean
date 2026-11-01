import Flapjack.Compiler.Encoders.X64.Machine.Congruence

/-!
# The decoder reads only the bytes it reports

`Congruence.lean` proves that two readers agreeing on the first sixteen bytes
decode to the same instruction.  That bound is what the closed-machine fetch
safety needs for a *fixed-width* instruction set, but x86-64 encodings are one
to ten bytes and the memory domain is only known to contain the bytes of the
instruction being executed.  This module proves the finer fact: the decoder
reads exactly the bytes below the length it reports, so two readers agreeing on
that prefix decode the same instruction.

`parseRM` is the base case: its reported `len` is exactly the number of bytes
it consumed (ModRM, optional SIB, optional displacement), and two readers
agreeing on that many bytes parse the same operand.
-/

namespace Flapjack.Compiler.Encoders.X64


set_option maxHeartbeats 4000000

/-- `parseRM` reads exactly the bytes its result reports: two readers agreeing
on the first `p.len` bytes from `off` parse the same operand. -/
theorem parseRM_congr_upto (r r' : Nat → BitVec 8) (off : Nat) (rexB : Bool) (p : ParsedRM)
    (hp : parseRM r off rexB = some p)
    (h : ∀ j, j < off + p.len → r j = r' j) : parseRM r' off rexB = some p := by
  have hoff : ∀ j, j < p.len → r (off + j) = r' (off + j) := fun j hj => h (off + j) (by omega)
  have hlen1 : 1 ≤ p.len := by
    have hp' := hp
    unfold parseRM at hp'; dsimp only at hp'
    split_ifs at hp' <;> cases hp' <;> simp
  have h0 : r off = r' off := hoff 0 (by omega)
  unfold parseRM at hp
  dsimp only at hp
  unfold parseRM
  by_cases h3 : (r off).toNat / 64 = 3
  · rw [if_pos h3] at hp
    rw [if_pos (by rw [← h0]; exact h3)]
    rw [h0] at hp
    exact hp
  · by_cases hr4 : (r off).toNat % 8 = 4
    · have hlen2 : 2 ≤ p.len := by
        have hp' := hp
        rw [if_neg h3, if_pos hr4] at hp'
        split_ifs at hp' <;> cases hp' <;> simp
      have h1 : r (off + 1) = r' (off + 1) := hoff 1 (by omega)
      rw [if_neg h3, if_pos hr4] at hp
      rw [if_neg (by rw [← h0]; exact h3), if_pos (by rw [← h0]; exact hr4)]
      by_cases hi4 : (r (off + 1)).toNat / 8 % 8 = 4
      · rw [if_neg (by simp [hi4])] at hp
        rw [if_neg (by rw [← h1]; simp [hi4])]
        by_cases hA : (r off).toNat / 64 = 0 ∧ (r (off + 1)).toNat % 8 = 5
        · rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)] at hp
          rw [if_pos (by rw [← h0, ← h1]; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)]
          have hlen : p.len = 6 := by
            have h := hp; simp only [Option.some.injEq] at h
            exact congrArg ParsedRM.len h.symm
          have himm : imm32 r (off + 2) = imm32 r' (off + 2) :=
            imm32_congr r r' (off + 2) (fun i hi => h i (by omega))
          rw [h0, h1, himm] at hp
          exact hp
        · rw [if_neg (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)] at hp
          rw [if_neg (by rw [← h0, ← h1]; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)]
          by_cases hB : (r off).toNat / 64 = 0
          · rw [if_pos hB] at hp
            rw [if_pos (by rw [← h0]; exact hB)]
            rw [h0, h1] at hp
            exact hp
          · rw [if_neg hB] at hp
            rw [if_neg (by rw [← h0]; exact hB)]
            by_cases hC : (r off).toNat / 64 = 1
            · rw [if_pos hC] at hp
              rw [if_pos (by rw [← h0]; exact hC)]
              have hlen : p.len = 3 := by
                have h := hp; simp only [Option.some.injEq] at h
                exact congrArg ParsedRM.len h.symm
              have himm : imm8 r (off + 2) = imm8 r' (off + 2) :=
                imm8_congr r r' (off + 2) (fun i hi => h i (by omega))
              rw [h0, h1, himm] at hp
              exact hp
            · rw [if_neg hC] at hp
              rw [if_neg (by rw [← h0]; exact hC)]
              have hlen : p.len = 6 := by
                have h := hp; simp only [Option.some.injEq] at h
                exact congrArg ParsedRM.len h.symm
              have himm : imm32 r (off + 2) = imm32 r' (off + 2) :=
                imm32_congr r r' (off + 2) (fun i hi => h i (by omega))
              rw [h0, h1, himm] at hp
              exact hp
      · rw [if_pos hi4] at hp
        simp at hp
    · rw [if_neg h3, if_neg hr4] at hp
      rw [if_neg (by rw [← h0]; exact h3), if_neg (by rw [← h0]; exact hr4)]
      by_cases hR : (r off).toNat / 64 = 0 ∧ (r off).toNat % 8 = 5
      · rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)] at hp
        rw [if_pos (by rw [← h0]; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)]
        have hlen : p.len = 5 := by
          have h := hp; simp only [Option.some.injEq] at h
          exact congrArg ParsedRM.len h.symm
        have himm : imm32 r (off + 1) = imm32 r' (off + 1) :=
          imm32_congr r r' (off + 1) (fun i hi => h i (by omega))
        rw [h0, himm] at hp
        exact hp
      · rw [if_neg (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)] at hp
        rw [if_neg (by rw [← h0]; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)]
        by_cases hB : (r off).toNat / 64 = 0
        · rw [if_pos hB] at hp
          rw [if_pos (by rw [← h0]; exact hB)]
          rw [h0] at hp
          exact hp
        · rw [if_neg hB] at hp
          rw [if_neg (by rw [← h0]; exact hB)]
          by_cases hC : (r off).toNat / 64 = 1
          · rw [if_pos hC] at hp
            rw [if_pos (by rw [← h0]; exact hC)]
            have hlen : p.len = 2 := by
              have h := hp; simp only [Option.some.injEq] at h
              exact congrArg ParsedRM.len h.symm
            have himm : imm8 r (off + 1) = imm8 r' (off + 1) :=
              imm8_congr r r' (off + 1) (fun i hi => h i (by omega))
            rw [h0, himm] at hp
            exact hp
          · rw [if_neg hC] at hp
            rw [if_neg (by rw [← h0]; exact hC)]
            have hlen : p.len = 5 := by
              have h := hp; simp only [Option.some.injEq] at h
              exact congrArg ParsedRM.len h.symm
            have himm : imm32 r (off + 1) = imm32 r' (off + 1) :=
              imm32_congr r r' (off + 1) (fun i hi => h i (by omega))
            rw [h0, himm] at hp
            exact hp

end Flapjack.Compiler.Encoders.X64
