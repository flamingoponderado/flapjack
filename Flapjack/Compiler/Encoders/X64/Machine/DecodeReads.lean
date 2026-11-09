module

public import Flapjack.Compiler.Encoders.X64.Machine.Congruence

@[expose] public section

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

/-- `decodeSSE` reads exactly the bytes below the length it reports, provided
`off` is the offset of the opcode byte after the `0F` escape (2 without a REX
prefix, 3 with one). -/
theorem decodeSSE_congr_upto (r r' : Nat → BitVec 8) (off : Nat) (mandatory : Nat)
    (hasRex rexW rexR rexB : Bool) (i : X64Insn) (len : Nat)
    (hoff : (off = 2 ∧ hasRex = false) ∨ (off = 3 ∧ hasRex = true))
    (hd : decodeSSE r off mandatory hasRex rexW rexR rexB = some (i, len))
    (h : ∀ j, j < len → r j = r' j) :
    decodeSSE r' off mandatory hasRex rexW rexR rexB = some (i, len) := by
  have hbase : 3 + (if hasRex then 1 else 0) = off + 1 := by
    rcases hoff with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  unfold decodeSSE at hd
  dsimp only at hd
  by_cases hm66 : mandatory = 0x66
  · rw [if_pos hm66] at hd
    by_cases hop2f : (r off).toNat = 0x2F
    · rw [if_pos hop2f] at hd
      cases hp : parseRM r (off + 1) rexB with
      | none => simp [hp] at hd
      | some p =>
        simp only [hp, Option.some.injEq, Prod.mk.injEq] at hd
        obtain ⟨hi, hlen⟩ := hd
        have hlen' : len = off + 1 + p.len := by rw [← hlen, hbase]
        have h0 : r off = r' off := h off (by omega)
        have hop' : (r' off).toNat = 0x2F := by rw [← h0]; exact hop2f
        have hpm : parseRM r' (off + 1) rexB = some p :=
          parseRM_congr_upto r r' (off + 1) rexB p hp (fun j hj => h j (by omega))
        unfold decodeSSE
        rw [if_pos hm66, if_pos hop', hpm]
        dsimp only
        rw [← hi, hlen]
    · rw [if_neg hop2f] at hd
      by_cases hop38 : (r off).toNat = 0x38
      · rw [if_pos hop38] at hd
        by_cases hb1 : (r (off + 1)).toNat = 0x29
        · rw [if_pos hb1] at hd
          cases hp : parseRM r (off + 2) rexB with
          | none => simp [hp] at hd
          | some p =>
            simp only [hp, Option.some.injEq, Prod.mk.injEq] at hd
            obtain ⟨hi, hlen⟩ := hd
            have hlen' : len = off + 2 + p.len := by rw [← hlen, hbase]
            have h0 : r off = r' off := h off (by omega)
            have h1 : r (off + 1) = r' (off + 1) := h (off + 1) (by omega)
            have hop' : (r' off).toNat = 0x38 := by rw [← h0]; exact hop38
            have hb1' : (r' (off + 1)).toNat = 0x29 := by rw [← h1]; exact hb1
            have hpm : parseRM r' (off + 2) rexB = some p :=
              parseRM_congr_upto r r' (off + 2) rexB p hp (fun j hj => h j (by omega))
            unfold decodeSSE
            rw [if_pos hm66, if_neg (by rw [← h0]; exact hop2f), if_pos hop']
            rw [if_pos hb1', hpm]
            dsimp only
            rw [← hi, hlen]
        · rw [if_neg hb1] at hd
          simp at hd
      · rw [if_neg hop38] at hd
        by_cases hop73 : (r off).toNat = 0x73
        · rw [if_pos hop73] at hd
          cases hp : parseRM r (off + 1) rexB with
          | none => simp [hp] at hd
          | some p =>
            rw [hp] at hd
            dsimp only at hd
            by_cases hmod : p.modBits = 3
            · rw [if_pos hmod] at hd
              by_cases hr2 : p.regBits = 2
              · rw [if_pos hr2] at hd
                simp only [Option.some.injEq, Prod.mk.injEq] at hd
                obtain ⟨hi, hlen⟩ := hd
                have hlen' : len = off + 2 + p.len := by rw [← hlen, hbase]
                have h0 : r off = r' off := h off (by omega)
                have hpm : parseRM r' (off + 1) rexB = some p :=
                  parseRM_congr_upto r r' (off + 1) rexB p hp (fun j hj => h j (by omega))
                have himm : r (off + 1 + p.len) = r' (off + 1 + p.len) := h _ (by omega)
                have hop' : (r' off).toNat = 0x73 := by rw [← h0]; exact hop73
                unfold decodeSSE
                rw [if_pos hm66, if_neg (by rw [← h0]; exact hop2f),
                  if_neg (by rw [← h0]; exact hop38), if_pos hop', hpm]
                dsimp only
                rw [hmod, if_pos hr2]
                simp only [reduceIte]
                rw [← himm, ← hi, hlen]
              · rw [if_neg hr2] at hd
                by_cases hr6 : p.regBits = 6
                · rw [if_pos hr6] at hd
                  simp only [Option.some.injEq, Prod.mk.injEq] at hd
                  obtain ⟨hi, hlen⟩ := hd
                  have hlen' : len = off + 2 + p.len := by rw [← hlen, hbase]
                  have h0 : r off = r' off := h off (by omega)
                  have hpm : parseRM r' (off + 1) rexB = some p :=
                    parseRM_congr_upto r r' (off + 1) rexB p hp (fun j hj => h j (by omega))
                  have himm : r (off + 1 + p.len) = r' (off + 1 + p.len) := h _ (by omega)
                  have hop' : (r' off).toNat = 0x73 := by rw [← h0]; exact hop73
                  unfold decodeSSE
                  rw [if_pos hm66, if_neg (by rw [← h0]; exact hop2f),
                    if_neg (by rw [← h0]; exact hop38), if_pos hop', hpm]
                  dsimp only
                  rw [hmod, if_neg hr2, if_pos hr6]
                  simp only [reduceIte]
                  rw [← himm, ← hi, hlen]
                · rw [if_neg hr6] at hd
                  by_cases hr3 : p.regBits = 3
                  · rw [if_pos hr3] at hd
                    simp only [Option.some.injEq, Prod.mk.injEq] at hd
                    obtain ⟨hi, hlen⟩ := hd
                    have hlen' : len = off + 2 + p.len := by rw [← hlen, hbase]
                    have h0 : r off = r' off := h off (by omega)
                    have hpm : parseRM r' (off + 1) rexB = some p :=
                      parseRM_congr_upto r r' (off + 1) rexB p hp (fun j hj => h j (by omega))
                    have himm : r (off + 1 + p.len) = r' (off + 1 + p.len) := h _ (by omega)
                    have hop' : (r' off).toNat = 0x73 := by rw [← h0]; exact hop73
                    unfold decodeSSE
                    rw [if_pos hm66, if_neg (by rw [← h0]; exact hop2f),
                      if_neg (by rw [← h0]; exact hop38), if_pos hop', hpm]
                    dsimp only
                    rw [hmod, if_neg hr2, if_neg hr6, if_pos hr3]
                    simp only [reduceIte]
                    rw [← himm, ← hi, hlen]
                  · rw [if_neg hr3] at hd
                    by_cases hr7 : p.regBits = 7
                    · rw [if_pos hr7] at hd
                      simp only [Option.some.injEq, Prod.mk.injEq] at hd
                      obtain ⟨hi, hlen⟩ := hd
                      have hlen' : len = off + 2 + p.len := by rw [← hlen, hbase]
                      have h0 : r off = r' off := h off (by omega)
                      have hpm : parseRM r' (off + 1) rexB = some p :=
                        parseRM_congr_upto r r' (off + 1) rexB p hp (fun j hj => h j (by omega))
                      have himm : r (off + 1 + p.len) = r' (off + 1 + p.len) := h _ (by omega)
                      have hop' : (r' off).toNat = 0x73 := by rw [← h0]; exact hop73
                      unfold decodeSSE
                      rw [if_pos hm66, if_neg (by rw [← h0]; exact hop2f),
                        if_neg (by rw [← h0]; exact hop38), if_pos hop', hpm]
                      dsimp only
                      rw [hmod, if_neg hr2, if_neg hr6, if_neg hr3, if_pos hr7]
                      simp only [reduceIte]
                      rw [← himm, ← hi, hlen]
                    · rw [if_neg hr7] at hd
                      simp at hd
            · rw [if_neg hmod] at hd
              simp at hd
        · rw [if_neg hop73] at hd
          by_cases hop54 : 0x54 ≤ (r off).toNat ∧ (r off).toNat ≤ 0x57
          · rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)] at hd
            cases hp : parseRM r (off + 1) rexB with
            | none => simp [hp] at hd
            | some p =>
              rw [hp] at hd
              dsimp only at hd
              cases hl : logicOfCode ((r off).toNat - 0x54) with
              | none => simp [hl] at hd
              | some logic =>
                simp only [hl, Option.some.injEq, Prod.mk.injEq] at hd
                obtain ⟨hi, hlen⟩ := hd
                have hlen' : len = off + 1 + p.len := by rw [← hlen, hbase]
                have h0 : r off = r' off := h off (by omega)
                have hop' : (r' off).toNat = (r off).toNat := by rw [← h0]
                have hop54' : 0x54 ≤ (r' off).toNat ∧ (r' off).toNat ≤ 0x57 := by
                  rw [hop']; exact hop54
                have hl' : logicOfCode ((r' off).toNat - 0x54) = some logic := by
                  rw [hop']; exact hl
                have hpm : parseRM r' (off + 1) rexB = some p :=
                  parseRM_congr_upto r r' (off + 1) rexB p hp (fun j hj => h j (by omega))
                unfold decodeSSE
                rw [if_pos hm66, if_neg (by rw [← h0]; exact hop2f),
                  if_neg (by rw [← h0]; exact hop38), if_neg (by rw [← h0]; exact hop73)]
                rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact hop54')]
                rw [hpm]
                dsimp only
                rw [hl', ← hi, hlen]
          · rw [if_neg (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)] at hd
            by_cases hop6e : (r off).toNat = 0x6E
            · rw [if_pos hop6e] at hd
              cases hp : parseRM r (off + 1) rexB with
              | none => simp [hp] at hd
              | some p =>
                simp only [hp, Option.some.injEq, Prod.mk.injEq] at hd
                obtain ⟨hi, hlen⟩ := hd
                have hlen' : len = off + 1 + p.len := by rw [← hlen, hbase]
                have h0 : r off = r' off := h off (by omega)
                have hop' : (r' off).toNat = 0x6E := by rw [← h0]; exact hop6e
                have hpm : parseRM r' (off + 1) rexB = some p :=
                  parseRM_congr_upto r r' (off + 1) rexB p hp (fun j hj => h j (by omega))
                unfold decodeSSE
                rw [if_pos hm66, if_neg (by rw [← h0]; exact hop2f),
                  if_neg (by rw [← h0]; exact hop38), if_neg (by rw [← h0]; exact hop73)]
                rw [if_neg (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)]
                rw [if_pos hop', hpm]
                dsimp only
                rw [← hi, hlen]
            · rw [if_neg hop6e] at hd
              by_cases hop7e : (r off).toNat = 0x7E
              · rw [if_pos hop7e] at hd
                cases hp : parseRM r (off + 1) rexB with
                | none => simp [hp] at hd
                | some p =>
                  simp only [hp, Option.some.injEq, Prod.mk.injEq] at hd
                  obtain ⟨hi, hlen⟩ := hd
                  have hlen' : len = off + 1 + p.len := by rw [← hlen, hbase]
                  have h0 : r off = r' off := h off (by omega)
                  have hop' : (r' off).toNat = 0x7E := by rw [← h0]; exact hop7e
                  have hpm : parseRM r' (off + 1) rexB = some p :=
                    parseRM_congr_upto r r' (off + 1) rexB p hp (fun j hj => h j (by omega))
                  unfold decodeSSE
                  rw [if_pos hm66, if_neg (by rw [← h0]; exact hop2f),
                    if_neg (by rw [← h0]; exact hop38), if_neg (by rw [← h0]; exact hop73)]
                  rw [if_neg (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)]
                  rw [if_neg (by rw [← h0]; exact hop6e), if_pos hop', hpm]
                  dsimp only
                  rw [← hi, hlen]
              · rw [if_neg hop7e] at hd
                by_cases hope6 : (r off).toNat = 0xE6
                · rw [if_pos hope6] at hd
                  cases hp : parseRM r (off + 1) rexB with
                  | none => simp [hp] at hd
                  | some p =>
                    simp only [hp, Option.some.injEq, Prod.mk.injEq] at hd
                    obtain ⟨hi, hlen⟩ := hd
                    have hlen' : len = off + 1 + p.len := by rw [← hlen, hbase]
                    have h0 : r off = r' off := h off (by omega)
                    have hop' : (r' off).toNat = 0xE6 := by rw [← h0]; exact hope6
                    have hpm : parseRM r' (off + 1) rexB = some p :=
                      parseRM_congr_upto r r' (off + 1) rexB p hp (fun j hj => h j (by omega))
                    unfold decodeSSE
                    rw [if_pos hm66, if_neg (by rw [← h0]; exact hop2f),
                      if_neg (by rw [← h0]; exact hop38), if_neg (by rw [← h0]; exact hop73)]
                    rw [if_neg (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)]
                    rw [if_neg (by rw [← h0]; exact hop6e), if_neg (by rw [← h0]; exact hop7e)]
                    rw [if_pos hop', hpm]
                    dsimp only
                    rw [← hi, hlen]
                · rw [if_neg hope6] at hd
                  simp at hd
  · rw [if_neg hm66] at hd
    by_cases hmf2 : mandatory = 0xF2
    · rw [if_pos hmf2] at hd
      by_cases hop10 : (r off).toNat = 0x10
      · rw [if_pos hop10] at hd
        cases hp : parseRM r (off + 1) rexB with
        | none => simp [hp] at hd
        | some p =>
          simp only [hp, Option.some.injEq, Prod.mk.injEq] at hd
          obtain ⟨hi, hlen⟩ := hd
          have hlen' : len = off + 1 + p.len := by rw [← hlen, hbase]
          have h0 : r off = r' off := h off (by omega)
          have hop' : (r' off).toNat = 0x10 := by rw [← h0]; exact hop10
          have hpm : parseRM r' (off + 1) rexB = some p :=
            parseRM_congr_upto r r' (off + 1) rexB p hp (fun j hj => h j (by omega))
          unfold decodeSSE
          rw [if_neg hm66, if_pos hmf2, if_pos hop', hpm]
          dsimp only
          rw [← hi, hlen]
      · rw [if_neg hop10] at hd
        by_cases hop51 : (r off).toNat = 0x51
        · rw [if_pos hop51] at hd
          cases hp : parseRM r (off + 1) rexB with
          | none => simp [hp] at hd
          | some p =>
            simp only [hp, Option.some.injEq, Prod.mk.injEq] at hd
            obtain ⟨hi, hlen⟩ := hd
            have hlen' : len = off + 1 + p.len := by rw [← hlen, hbase]
            have h0 : r off = r' off := h off (by omega)
            have hop' : (r' off).toNat = 0x51 := by rw [← h0]; exact hop51
            have hpm : parseRM r' (off + 1) rexB = some p :=
              parseRM_congr_upto r r' (off + 1) rexB p hp (fun j hj => h j (by omega))
            unfold decodeSSE
            rw [if_neg hm66, if_pos hmf2, if_neg (by rw [← h0]; exact hop10), if_pos hop', hpm]
            dsimp only
            rw [← hi, hlen]
        · rw [if_neg hop51] at hd
          by_cases hop58 : 0x58 ≤ (r off).toNat ∧ (r off).toNat ≤ 0x5F
          · rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)] at hd
            cases hp : parseRM r (off + 1) rexB with
            | none => simp [hp] at hd
            | some p =>
              rw [hp] at hd
              dsimp only at hd
              cases hb : sseBinopOfCode ((r off).toNat - 0x58) with
              | none => simp [hb] at hd
              | some bop =>
                simp only [hb, Option.some.injEq, Prod.mk.injEq] at hd
                obtain ⟨hi, hlen⟩ := hd
                have hlen' : len = off + 1 + p.len := by rw [← hlen, hbase]
                have h0 : r off = r' off := h off (by omega)
                have hop' : (r' off).toNat = (r off).toNat := by rw [← h0]
                have hop58' : 0x58 ≤ (r' off).toNat ∧ (r' off).toNat ≤ 0x5F := by
                  rw [hop']; exact hop58
                have hb' : sseBinopOfCode ((r' off).toNat - 0x58) = some bop := by
                  rw [hop']; exact hb
                have hpm : parseRM r' (off + 1) rexB = some p :=
                  parseRM_congr_upto r r' (off + 1) rexB p hp (fun j hj => h j (by omega))
                unfold decodeSSE
                rw [if_neg hm66, if_pos hmf2, if_neg (by rw [← h0]; exact hop10),
                  if_neg (by rw [← h0]; exact hop51)]
                rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact hop58')]
                rw [hpm]
                dsimp only
                rw [hb', ← hi, hlen]
          · rw [if_neg (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)] at hd
            by_cases hope6 : (r off).toNat = 0xE6
            · rw [if_pos hope6] at hd
              cases hp : parseRM r (off + 1) rexB with
              | none => simp [hp] at hd
              | some p =>
                simp only [hp, Option.some.injEq, Prod.mk.injEq] at hd
                obtain ⟨hi, hlen⟩ := hd
                have hlen' : len = off + 1 + p.len := by rw [← hlen, hbase]
                have h0 : r off = r' off := h off (by omega)
                have hop' : (r' off).toNat = 0xE6 := by rw [← h0]; exact hope6
                have hpm : parseRM r' (off + 1) rexB = some p :=
                  parseRM_congr_upto r r' (off + 1) rexB p hp (fun j hj => h j (by omega))
                unfold decodeSSE
                rw [if_neg hm66, if_pos hmf2, if_neg (by rw [← h0]; exact hop10),
                  if_neg (by rw [← h0]; exact hop51)]
                rw [if_neg (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)]
                rw [if_pos hop', hpm]
                dsimp only
                rw [← hi, hlen]
            · rw [if_neg hope6] at hd
              simp at hd
    · rw [if_neg hmf2] at hd
      by_cases hmf3 : mandatory = 0xF3
      · rw [if_pos hmf3] at hd
        by_cases hope6 : (r off).toNat = 0xE6
        · rw [if_pos hope6] at hd
          cases hp : parseRM r (off + 1) rexB with
          | none => simp [hp] at hd
          | some p =>
            simp only [hp, Option.some.injEq, Prod.mk.injEq] at hd
            obtain ⟨hi, hlen⟩ := hd
            have hlen' : len = off + 1 + p.len := by rw [← hlen, hbase]
            have h0 : r off = r' off := h off (by omega)
            have hop' : (r' off).toNat = 0xE6 := by rw [← h0]; exact hope6
            have hpm : parseRM r' (off + 1) rexB = some p :=
              parseRM_congr_upto r r' (off + 1) rexB p hp (fun j hj => h j (by omega))
            unfold decodeSSE
            rw [if_neg hm66, if_neg hmf2, if_pos hmf3, if_pos hop', hpm]
            dsimp only
            rw [← hi, hlen]
        · rw [if_neg hope6] at hd
          simp at hd
      · rw [if_neg hmf3] at hd
        simp at hd


end Flapjack.Compiler.Encoders.X64
