import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.LogicalShiftedRegister

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

/-!
# `MultiplyHigh` and `MultiplyAddSub@64`: the `longMul` lowering

`arm8_ast` lowers `Arith (LongMul high low left right)` to two instructions:
`MultiplyHigh (false, right, left, high)` followed by
`MultiplyAddSub@64 (1, false, right, 31, left, low)`.  The first writes the top
64 bits of the unsigned 128-bit product of the two sources; the second writes
the low 64 bits (`left * right + ZR`), matching the `longMul` update
`(r / 2 ^ 64, r % 2 ^ 64)` with `r = left.toNat * right.toNat`.

This module records the words, the `Encode`/`Decode` inverses, the `Run`
semantics and the high-half arithmetic identity.  The case theorem of
`encoder_correct arm8TargetL3` is not built here.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The word emitted for `MultiplyHigh`: HOL's `e_data` term
`0b10011011 ++ (!u) ++ 10 ++ Rm ++ 011111 ++ Rn ++ Rd` (Flapjack
infrastructure: a readable abbreviation for a mechanically rendered term). -/
def arm8MultiplyHighWord (u : Bool) (rm rn rd : BitVec 5) : BitVec 32 :=
  BitVec.setWidth 32 ((BitVec.ofNat 8 155) ++
    BitVec.setWidth 24 (holV2w 1 [!u] ++
      BitVec.setWidth 23 ((BitVec.ofNat 2 2) ++
        BitVec.setWidth 21 (rm ++
          BitVec.setWidth 16 ((BitVec.ofNat 6 31) ++
            BitVec.setWidth 10 (rn ++ rd))))))

/-- `e_data` of `MultiplyHigh` is the multiply-high word (Flapjack
infrastructure; no separately named HOL declaration). -/
theorem arm8EData_multiplyHigh (u : Bool) (rm rn rd : BitVec 5) :
    e_data (.MultiplyHigh (u, (rm, (rn, rd)))) =
      MachineCode.ARM8 (arm8MultiplyHighWord u rm rn rd) := by
  rfl

/-- `Encode` of `MultiplyHigh` is the multiply-high word (Flapjack
infrastructure; no separately named HOL declaration). -/
theorem arm8Encode_multiplyHigh (u : Bool) (rm rn rd : BitVec 5) :
    Encode (.Data (.MultiplyHigh (u, (rm, (rn, rd))))) =
      MachineCode.ARM8 (arm8MultiplyHighWord u rm rn rd) := by
  simp only [Encode, arm8EData_multiplyHigh]

/-- The rendered `Decode` inverts `arm8MultiplyHighWord` for the unsigned form
used by `arm8_ast`. -/
theorem arm8Decode_multiplyHigh (rm rn rd : BitVec 5) :
    Decode (arm8MultiplyHighWord false rm rn rd) =
      instruction.Data (Data.MultiplyHigh (false, (rm, (rn, rd)))) := by
  simp only [arm8MultiplyHighWord, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  simp [holV2w_one_true, holV2w_five]

/-- `Run` of `MultiplyHigh`: write the top 64 bits of the extended product of
`Rn` and `Rm` to `Rd`. -/
theorem arm8Run_multiplyHigh (u : Bool) (rm rn rd : BitVec 5) (st : arm8_state) :
    Run (instruction.Data (Data.MultiplyHigh (u, (rm, (rn, rd))))) st =
      «write'X» (holWordExtract 64 127 64
        (ExtendWord (TM := 64) (TN := 128) (X (TN := 64) rn st, u) *
          ExtendWord (TM := 64) (TN := 128) (X (TN := 64) rm st, u)), rd) st := by
  simp only [Run, «dfn'MultiplyHigh»]

/-- The high half of the unsigned 128-bit product is `r / 2 ^ 64` with
`r = a.toNat * b.toNat`. -/
theorem arm8MultiplyHigh_high (a b : BitVec 64) :
    holWordExtract 64 127 64 (BitVec.setWidth 128 a * BitVec.setWidth 128 b) =
      BitVec.ofNat 64 ((a.toNat * b.toNat) / 2 ^ 64) := by
  have ha : (BitVec.setWidth 128 a).toNat = a.toNat := by
    rw [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (by have := a.isLt; omega)
  have hb : (BitVec.setWidth 128 b).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (by have := b.isLt; omega)
  have hlt : a.toNat * b.toNat < 2 ^ 128 := by
    have ha' := a.isLt
    have hb' := b.isLt
    calc a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha' hb'
      _ = 2 ^ 128 := by norm_num
  have hprod : (BitVec.setWidth 128 a * BitVec.setWidth 128 b).toNat
      = a.toNat * b.toNat % 2 ^ 128 := by
    rw [BitVec.toNat_mul, ha, hb]
  have hexp : min 127 (128 - 1) + 1 - 64 = 64 := by norm_num
  simp only [Flapjack.RiscV.L3.holWordExtract, hprod, hexp]
  rw [Nat.mod_eq_of_lt hlt, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega)]
  have hN' : (a.toNat * b.toNat) / 2 ^ 64 < 2 ^ 128 := by omega
  rw [BitVec.setWidth, dif_neg (by norm_num : ¬ 128 ≤ 64), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hN']

/-- The word emitted for `MultiplyAddSub@64`: HOL's `e_data` term
`0b10011011000 ++ Rm ++ o0 ++ Ra ++ Rn ++ Rd` (Flapjack infrastructure: a
readable abbreviation for a mechanically rendered term). -/
def arm8MultiplyAddSubWord (o0 : Bool) (rm ra rn rd : BitVec 5) : BitVec 32 :=
  BitVec.setWidth 32 ((BitVec.ofNat 11 1240) ++
    BitVec.setWidth 21 (rm ++
      BitVec.setWidth 16 (holV2w 1 [o0] ++
        BitVec.setWidth 15 (ra ++
          BitVec.setWidth 10 (rn ++ rd)))))

/-- `e_data` of `MultiplyAddSub@64` is the multiply-add-sub word (Flapjack
infrastructure; no separately named HOL declaration). -/
theorem arm8EData_multiplyAddSub (o0 : Bool) (rm ra rn rd : BitVec 5) :
    e_data (.«MultiplyAddSub@64» ((1 : BitVec 64), (o0, (rm, (ra, (rn, rd)))))) =
      MachineCode.ARM8 (arm8MultiplyAddSubWord o0 rm ra rn rd) := by
  rfl

/-- `Encode` of `MultiplyAddSub@64` is the multiply-add-sub word (Flapjack
infrastructure; no separately named HOL declaration). -/
theorem arm8Encode_multiplyAddSub (o0 : Bool) (rm ra rn rd : BitVec 5) :
    Encode (.Data (.«MultiplyAddSub@64» ((1 : BitVec 64), (o0, (rm, (ra, (rn, rd))))))) =
      MachineCode.ARM8 (arm8MultiplyAddSubWord o0 rm ra rn rd) := by
  simp only [Encode, arm8EData_multiplyAddSub]

/-- The rendered `Decode` inverts `arm8MultiplyAddSubWord` for the add form used
by `arm8_ast`. -/
theorem arm8Decode_multiplyAddSub (rm ra rn rd : BitVec 5) :
    Decode (arm8MultiplyAddSubWord false rm ra rn rd) =
      instruction.Data (Data.«MultiplyAddSub@64»
        ((1 : BitVec 64), (false, (rm, (ra, (rn, rd)))))) := by
  simp only [arm8MultiplyAddSubWord, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  simp [holV2w_one_false, holV2w_five]

/-- `Run` of `MultiplyAddSub@64`: write `Ra + Rn * Rm` (or the difference when
`sub_op` is set) to `Rd`. -/
theorem arm8Run_multiplyAddSub (o0 : Bool) (rm ra rn rd : BitVec 5) (st : arm8_state) :
    Run (instruction.Data (Data.«MultiplyAddSub@64» ((1 : BitVec 64), (o0, (rm, (ra, (rn, rd))))))) st =
      «write'X» ((if o0 then X (TN := 64) ra st - X (TN := 64) rn st * X (TN := 64) rm st
        else X (TN := 64) ra st + X (TN := 64) rn st * X (TN := 64) rm st), rd) st := by
  simp only [Run, «dfn'MultiplyAddSub»]


/-! ## The single-step reductions of the two `longMul` instructions -/

/-- One `arm8Next` step on the `MultiplyHigh` word writes the top half of the
unsigned 128-bit product of `Rn` and `Rm` to register `n`. -/
theorem arm8Next_multiplyHigh (ms : arm8_state) (rm rn : BitVec 5) (n : Nat)
    (hn : n < 32) (h31 : n ≠ 31) (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((arm8MultiplyHighWord false rm rn (BitVec.ofNat 5 n) >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((arm8MultiplyHighWord false rm rn (BitVec.ofNat 5 n) >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((arm8MultiplyHighWord false rm rn (BitVec.ofNat 5 n) >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((arm8MultiplyHighWord false rm rn (BitVec.ofNat 5 n) >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    arm8Next ms =
      { ms with branch_hint := none, REG := holUpdate (BitVec.ofNat 5 n) (holWordExtract 64 127 64 (BitVec.setWidth 128 (X (TN := 64) rn ms) * BitVec.setWidth 128 (X (TN := 64) rm ms))) ms.REG, PC := ms.PC + 4 } := by
  have hdec : Decode (arm8MultiplyHighWord false rm rn (BitVec.ofNat 5 n)) =
      instruction.Data (Data.MultiplyHigh (false, (rm, (rn, BitVec.ofNat 5 n)))) :=
    arm8Decode_multiplyHigh rm rn _
  have hbr : (Run (instruction.Data (Data.MultiplyHigh (false, (rm, (rn, BitVec.ofNat 5 n))))) ({ ms with branch_hint := none })).branch_hint = none := by
    rw [arm8Run_multiplyHigh]
    rw [arm8WriteX_of_valid _ _ h31 hn]
  have hexc : (Run (instruction.Data (Data.MultiplyHigh (false, (rm, (rn, BitVec.ofNat 5 n))))) ({ ms with branch_hint := none })).exception = exception.NoException := by
    rw [arm8Run_multiplyHigh]
    rw [arm8WriteX_of_valid _ _ h31 hn]
    simpa using hexc0
  have hn' := arm8Next_word ms (arm8MultiplyHighWord false rm rn (BitVec.ofNat 5 n))
    (instruction.Data (Data.MultiplyHigh (false, (rm, (rn, BitVec.ofNat 5 n)))))
    hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  unfold arm8Next
  rw [hn', arm8Run_multiplyHigh, arm8WriteX_of_valid _ _ h31 hn]
  simp only [ExtendWord, Bool.false_eq_true, if_false, holThe]
  rfl

/-- One `arm8Next` step on the `MultiplyAddSub@64` word writes `Ra + Rn * Rm`
to register `n`. -/
theorem arm8Next_multiplyAddSub (ms : arm8_state) (rm ra rn : BitVec 5) (n : Nat)
    (hn : n < 32) (h31 : n ≠ 31) (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((arm8MultiplyAddSubWord false rm ra rn (BitVec.ofNat 5 n) >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((arm8MultiplyAddSubWord false rm ra rn (BitVec.ofNat 5 n) >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((arm8MultiplyAddSubWord false rm ra rn (BitVec.ofNat 5 n) >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((arm8MultiplyAddSubWord false rm ra rn (BitVec.ofNat 5 n) >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    arm8Next ms =
      { ms with branch_hint := none, REG := holUpdate (BitVec.ofNat 5 n) (X (TN := 64) ra ms + X (TN := 64) rn ms * X (TN := 64) rm ms) ms.REG, PC := ms.PC + 4 } := by
  have hdec : Decode (arm8MultiplyAddSubWord false rm ra rn (BitVec.ofNat 5 n)) =
      instruction.Data (Data.«MultiplyAddSub@64» ((1 : BitVec 64), (false, (rm, (ra, (rn, BitVec.ofNat 5 n)))))) :=
    arm8Decode_multiplyAddSub rm ra rn _
  have hbr : (Run (instruction.Data (Data.«MultiplyAddSub@64» ((1 : BitVec 64), (false, (rm, (ra, (rn, BitVec.ofNat 5 n))))))) ({ ms with branch_hint := none })).branch_hint = none := by
    rw [arm8Run_multiplyAddSub]
    rw [arm8WriteX_of_valid _ _ h31 hn]
  have hexc : (Run (instruction.Data (Data.«MultiplyAddSub@64» ((1 : BitVec 64), (false, (rm, (ra, (rn, BitVec.ofNat 5 n))))))) ({ ms with branch_hint := none })).exception = exception.NoException := by
    rw [arm8Run_multiplyAddSub]
    rw [arm8WriteX_of_valid _ _ h31 hn]
    simpa using hexc0
  have hn' := arm8Next_word ms (arm8MultiplyAddSubWord false rm ra rn (BitVec.ofNat 5 n))
    (instruction.Data (Data.«MultiplyAddSub@64» ((1 : BitVec 64), (false, (rm, (ra, (rn, BitVec.ofNat 5 n)))))))
    hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  unfold arm8Next
  rw [hn', arm8Run_multiplyAddSub, arm8WriteX_of_valid _ _ h31 hn]
  simp only [holThe]
  rfl


/-! ## Agreement lemmas for the two `longMul` steps -/

/-- Reading a non-`SP` register commutes with `Arm8L3Agree`. -/
theorem arm8X_congr {d : BitVec 64 → Prop} {s t : arm8_state} (h : Arm8L3Agree d s t)
    {n : BitVec 5} (hn : n ≠ 31#5) : X (TN := 64) n s = X (TN := 64) n t := by
  simp [X, h.reg, hn]

/-- The zero register reads as zero in every state, so `X` agrees there without
a register-agreement hypothesis. -/
theorem arm8X_congr_or_zero {d : BitVec 64 → Prop} {s t : arm8_state}
    (h : Arm8L3Agree d s t) (n : BitVec 5) : X (TN := 64) n s = X (TN := 64) n t := by
  by_cases hn : n = 31#5
  · rw [hn, arm8X_zero, arm8X_zero]
  · exact arm8X_congr h hn

/-- Applying `arm8Next` to two states that agree on `d` and carry the
`MultiplyHigh` word gives states that still agree. -/
theorem arm8Next_multiplyHigh_agree (d : BitVec 64 → Prop) (s t : arm8_state)
    (h : Arm8L3Agree d s t) (hok : arm8Ok s = true)
    (rm rn : BitVec 5) (n : Nat) (hn : n < 32) (h31 : n ≠ 31)
    (hrn : rn ≠ 31#5) (hrm : rm ≠ 31#5)
    (hf : ∀ j, j < 4 → d (t.PC + BitVec.ofNat 64 j))
    (hb0 : t.MEM t.PC = BitVec.ofNat 8 ((arm8MultiplyHighWord false rm rn (BitVec.ofNat 5 n) >>> 0).toNat))
    (hb1 : t.MEM (t.PC + 1) = BitVec.ofNat 8 ((arm8MultiplyHighWord false rm rn (BitVec.ofNat 5 n) >>> 8).toNat))
    (hb2 : t.MEM (t.PC + 2) = BitVec.ofNat 8 ((arm8MultiplyHighWord false rm rn (BitVec.ofNat 5 n) >>> 16).toNat))
    (hb3 : t.MEM (t.PC + 3) = BitVec.ofNat 8 ((arm8MultiplyHighWord false rm rn (BitVec.ofNat 5 n) >>> 24).toNat)) :
    Arm8L3Agree d (arm8Next s) (arm8Next t) := by
  have hokt : arm8Ok t = true := by rw [← arm8Ok_congr h]; exact hok
  obtain ⟨hel, he0, _, _, _, hexc0, halign⟩ := (arm8Ok_iff s).mp hok
  obtain ⟨helt, he0t, _, _, _, hexc0t, halignt⟩ := (arm8Ok_iff t).mp hokt
  have hal : Aligned (TN := 64) (s.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa [← h.pc] using (holAligned_iff 2 s.PC).mp halign
  have halt : Aligned (TN := 64) (t.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 t.PC).mp halignt
  have hs0 : s.MEM s.PC = BitVec.ofNat 8 ((arm8MultiplyHighWord false rm rn (BitVec.ofNat 5 n) >>> 0).toNat) := by
    rw [h.pc]
    exact (h.mem t.PC (by simpa using hf 0 (by omega))).trans hb0
  have hs1 : s.MEM (s.PC + 1) = BitVec.ofNat 8 ((arm8MultiplyHighWord false rm rn (BitVec.ofNat 5 n) >>> 8).toNat) := by
    rw [h.pc]
    exact (h.mem (t.PC + 1) (by simpa using hf 1 (by omega))).trans hb1
  have hs2 : s.MEM (s.PC + 2) = BitVec.ofNat 8 ((arm8MultiplyHighWord false rm rn (BitVec.ofNat 5 n) >>> 16).toNat) := by
    rw [h.pc]
    exact (h.mem (t.PC + 2) (by simpa using hf 2 (by omega))).trans hb2
  have hs3 : s.MEM (s.PC + 3) = BitVec.ofNat 8 ((arm8MultiplyHighWord false rm rn (BitVec.ofNat 5 n) >>> 24).toNat) := by
    rw [h.pc]
    exact (h.mem (t.PC + 3) (by simpa using hf 3 (by omega))).trans hb3
  have hss := arm8Next_multiplyHigh s rm rn n hn h31 hexc0 hs0 hs1 hs2 hs3 hal he0 hel
  have htt := arm8Next_multiplyHigh t rm rn n hn h31 hexc0t hb0 hb1 hb2 hb3 halt he0t helt
  rw [hss, htt]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [h.pc]
  · simp only [h.reg, arm8X_congr h hrn, arm8X_congr h hrm]
  · simp [h.pstate]
  · simp [h.sctlr]
  · simp [h.tcr]
  · simp [h.exc]
  · intro a ha
    simp only [h.mem a ha]

/-- Applying `arm8Next` to two states that agree on `d` and carry the
`MultiplyAddSub@64` word gives states that still agree. -/
theorem arm8Next_multiplyAddSub_agree (d : BitVec 64 → Prop) (s t : arm8_state)
    (h : Arm8L3Agree d s t) (hok : arm8Ok s = true)
    (rm ra rn : BitVec 5) (n : Nat) (hn : n < 32) (h31 : n ≠ 31)
    (hrn : rn ≠ 31#5) (hrm : rm ≠ 31#5)
    (hf : ∀ j, j < 4 → d (t.PC + BitVec.ofNat 64 j))
    (hb0 : t.MEM t.PC = BitVec.ofNat 8 ((arm8MultiplyAddSubWord false rm ra rn (BitVec.ofNat 5 n) >>> 0).toNat))
    (hb1 : t.MEM (t.PC + 1) = BitVec.ofNat 8 ((arm8MultiplyAddSubWord false rm ra rn (BitVec.ofNat 5 n) >>> 8).toNat))
    (hb2 : t.MEM (t.PC + 2) = BitVec.ofNat 8 ((arm8MultiplyAddSubWord false rm ra rn (BitVec.ofNat 5 n) >>> 16).toNat))
    (hb3 : t.MEM (t.PC + 3) = BitVec.ofNat 8 ((arm8MultiplyAddSubWord false rm ra rn (BitVec.ofNat 5 n) >>> 24).toNat)) :
    Arm8L3Agree d (arm8Next s) (arm8Next t) := by
  have hokt : arm8Ok t = true := by rw [← arm8Ok_congr h]; exact hok
  obtain ⟨hel, he0, _, _, _, hexc0, halign⟩ := (arm8Ok_iff s).mp hok
  obtain ⟨helt, he0t, _, _, _, hexc0t, halignt⟩ := (arm8Ok_iff t).mp hokt
  have hal : Aligned (TN := 64) (s.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa [← h.pc] using (holAligned_iff 2 s.PC).mp halign
  have halt : Aligned (TN := 64) (t.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 t.PC).mp halignt
  have hs0 : s.MEM s.PC = BitVec.ofNat 8 ((arm8MultiplyAddSubWord false rm ra rn (BitVec.ofNat 5 n) >>> 0).toNat) := by
    rw [h.pc]
    exact (h.mem t.PC (by simpa using hf 0 (by omega))).trans hb0
  have hs1 : s.MEM (s.PC + 1) = BitVec.ofNat 8 ((arm8MultiplyAddSubWord false rm ra rn (BitVec.ofNat 5 n) >>> 8).toNat) := by
    rw [h.pc]
    exact (h.mem (t.PC + 1) (by simpa using hf 1 (by omega))).trans hb1
  have hs2 : s.MEM (s.PC + 2) = BitVec.ofNat 8 ((arm8MultiplyAddSubWord false rm ra rn (BitVec.ofNat 5 n) >>> 16).toNat) := by
    rw [h.pc]
    exact (h.mem (t.PC + 2) (by simpa using hf 2 (by omega))).trans hb2
  have hs3 : s.MEM (s.PC + 3) = BitVec.ofNat 8 ((arm8MultiplyAddSubWord false rm ra rn (BitVec.ofNat 5 n) >>> 24).toNat) := by
    rw [h.pc]
    exact (h.mem (t.PC + 3) (by simpa using hf 3 (by omega))).trans hb3
  have hss := arm8Next_multiplyAddSub s rm ra rn n hn h31 hexc0 hs0 hs1 hs2 hs3 hal he0 hel
  have htt := arm8Next_multiplyAddSub t rm ra rn n hn h31 hexc0t hb0 hb1 hb2 hb3 halt he0t helt
  rw [hss, htt]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [h.pc]
  · simp only [h.reg, arm8X_congr_or_zero h ra, arm8X_congr h hrn, arm8X_congr h hrm]
  · simp [h.pstate]
  · simp [h.sctlr]
  · simp [h.tcr]
  · simp [h.exc]
  · intro a ha
    simp only [h.mem a ha]


/-- The `MultiplyHigh` step leaves memory unchanged. -/
theorem arm8Next_multiplyHigh_mem (ms : arm8_state) (rm rn : BitVec 5) (n : Nat)
    (hn : n < 32) (h31 : n ≠ 31) (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((arm8MultiplyHighWord false rm rn (BitVec.ofNat 5 n) >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((arm8MultiplyHighWord false rm rn (BitVec.ofNat 5 n) >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((arm8MultiplyHighWord false rm rn (BitVec.ofNat 5 n) >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((arm8MultiplyHighWord false rm rn (BitVec.ofNat 5 n) >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    ∀ x, (arm8Next ms).MEM x = ms.MEM x := by
  rw [arm8Next_multiplyHigh ms rm rn n hn h31 hexc0 h0 h1 h2 h3 hal he0 hel]
  intro x
  rfl

/-- The `MultiplyAddSub@64` step leaves memory unchanged. -/
theorem arm8Next_multiplyAddSub_mem (ms : arm8_state) (rm ra rn : BitVec 5) (n : Nat)
    (hn : n < 32) (h31 : n ≠ 31) (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((arm8MultiplyAddSubWord false rm ra rn (BitVec.ofNat 5 n) >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((arm8MultiplyAddSubWord false rm ra rn (BitVec.ofNat 5 n) >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((arm8MultiplyAddSubWord false rm ra rn (BitVec.ofNat 5 n) >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((arm8MultiplyAddSubWord false rm ra rn (BitVec.ofNat 5 n) >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    ∀ x, (arm8Next ms).MEM x = ms.MEM x := by
  rw [arm8Next_multiplyAddSub ms rm ra rn n hn h31 hexc0 h0 h1 h2 h3 hal he0 hel]
  intro x
  rfl


/-- The encoded bytes of the `longMul` lowering: `MultiplyHigh` then
`MultiplyAddSub@64` against the zero register. -/
theorem arm8Enc_longMul (destinationLeft destinationRight sourceLeft sourceRight : Nat) :
    arm8Enc (.inst (.arith (.longMul destinationLeft destinationRight sourceLeft sourceRight))) =
      arm8Encode (.Data (.MultiplyHigh (false, BitVec.ofNat 5 sourceRight,
        BitVec.ofNat 5 sourceLeft, BitVec.ofNat 5 destinationLeft))) ++
      arm8Encode (.Data (.«MultiplyAddSub@64» (1, false, BitVec.ofNat 5 sourceRight, 31,
        BitVec.ofNat 5 sourceLeft, BitVec.ofNat 5 destinationRight))) := by
  rw [arm8Enc]
  simp [arm8Ast]

/-- The `longMul` lowering is eight bytes long. -/
theorem arm8Enc_longMul_length (destinationLeft destinationRight sourceLeft sourceRight : Nat) :
    (arm8Enc (.inst (.arith (.longMul destinationLeft destinationRight sourceLeft sourceRight)))).length = 8 := by
  rw [arm8Enc_longMul]
  simp [arm8Encode_length]


/-- The bytes emitted for `MultiplyHigh`. -/
theorem arm8EncodeBytes_multiplyHigh (rm rn rd : BitVec 5) :
    arm8Encode (.Data (.MultiplyHigh (false, rm, rn, rd))) =
      [BitVec.ofNat 8 ((arm8MultiplyHighWord false rm rn rd >>> 0).toNat),
       BitVec.ofNat 8 ((arm8MultiplyHighWord false rm rn rd >>> 8).toNat),
       BitVec.ofNat 8 ((arm8MultiplyHighWord false rm rn rd >>> 16).toNat),
       BitVec.ofNat 8 ((arm8MultiplyHighWord false rm rn rd >>> 24).toNat)] := by
  simp [arm8Encode, arm8Encode_multiplyHigh]


theorem arm8EncodeBytes_multiplyAddSub (rm ra rn rd : BitVec 5) :
    arm8Encode (.Data (.«MultiplyAddSub@64» ((1 : BitVec 64), (false, (rm, (ra, (rn, rd))))))) =
      [BitVec.ofNat 8 ((arm8MultiplyAddSubWord false rm ra rn rd >>> 0).toNat),
       BitVec.ofNat 8 ((arm8MultiplyAddSubWord false rm ra rn rd >>> 8).toNat),
       BitVec.ofNat 8 ((arm8MultiplyAddSubWord false rm ra rn rd >>> 16).toNat),
       BitVec.ofNat 8 ((arm8MultiplyAddSubWord false rm ra rn rd >>> 24).toNat)] := by
  unfold arm8Encode
  rw [arm8Encode_multiplyAddSub]


/-- The value `MultiplyHigh` writes, read off the two source registers of a
valid machine state. -/
theorem arm8MultiplyHigh_extract (ms : arm8_state) (sl sr : Nat)
    (hsl : sl < 32) (hsl31 : sl ≠ 31) (hsr : sr < 32) (hsr31 : sr ≠ 31) :
    holWordExtract 64 127 64
      (BitVec.setWidth 128 (X (TN := 64) (BitVec.ofNat 5 sl) ms) *
        BitVec.setWidth 128 (X (TN := 64) (BitVec.ofNat 5 sr) ms)) =
      BitVec.ofNat 64 ((ms.REG (BitVec.ofNat 5 sl)).toNat * (ms.REG (BitVec.ofNat 5 sr)).toNat / 2 ^ 64) := by
  rw [arm8X_of_valid _ hsl31 hsl, arm8X_of_valid _ hsr31 hsr, arm8MultiplyHigh_high]


/-- Reading a register other than the one just written is unchanged. -/
theorem arm8X_update_other (st : arm8_state) (a b : BitVec 5) (v : BitVec 64) (h : a ≠ b) :
    X (TN := 64) a { st with REG := holUpdate b v st.REG } = X (TN := 64) a st := by
  simp [X, Flapjack.RiscV.L3.holUpdate, Ne.symm h]


/-- A 64-bit product is the `ofNat` of the product of the `toNat`s. -/
theorem arm8Mul_ofNat (a b : BitVec 64) :
    a * b = BitVec.ofNat 64 (a.toNat * b.toNat) := by
  rfl


/-- Reading a register other than the written one through the intermediate
`longMul` state is unchanged. -/
theorem arm8X_longMulT1 (ms : arm8_state) (hi : BitVec 64) (d : BitVec 5)
    {a : BitVec 5} (h : a ≠ d) :
    X (TN := 64) a { ms with branch_hint := none, REG := holUpdate d hi ms.REG, PC := ms.PC + 4 } =
      X (TN := 64) a ms := by
  simp [X, Flapjack.RiscV.L3.holUpdate, Ne.symm h]


end Flapjack.Compiler.Encoders.Arm8.L3
