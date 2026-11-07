import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.MoveWide

set_option maxHeartbeats 4000000

/-!
# L3 ARMv8 `LogicalImmediate` encode/decode inverse and execution

The `LogicalImmediate` half of the `Const` case of
`encoder_correct arm8TargetL3`:

* `arm8LogicalImmediateWord`: the 32-bit word `Encode` emits for
  `LogicalImmediate@64 (1, opc, setflags, imm, rn, rd)` when `EncodeBitMask`
  accepts `imm` and `EncodeLogicalOp` accepts `(opc, setflags)`.
* `EncodeBitMask_spec`: `EncodeBitMask` only succeeds when the mask it
  recomputes through `DecodeBitMasks` is the original immediate; this is the
  guard that lets `Decode` recover `imm` exactly.
* `arm8Decode_logicalImmediate`: the full rendered `Decode` inverts the word.
* `arm8Run_logicalImmediate_orr`: the rendered `Run` of the `ORR`/no-flags
  form with `rn = 31` (the `Const` lowering) writes the immediate.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Asm

/-- The 32-bit word `Encode` emits for
`LogicalImmediate@64 (1, opc, setflags, imm, rn, rd)`. -/
def arm8LogicalImmediateWord (opc : BitVec 2) (N : BitVec 1) (imms immr : BitVec 6)
    (rn rd : BitVec 5) : BitVec 32 :=
  BitVec.setWidth 32 ((BitVec.ofNat 1 1) ++
    (BitVec.setWidth 31 (opc ++
      (BitVec.setWidth 29 ((BitVec.ofNat 6 36) ++
        (BitVec.setWidth 23 (N ++
          (BitVec.setWidth 22 (immr ++
            (BitVec.setWidth 16 (imms ++
              (BitVec.setWidth 10 (rn ++ rd)))))))))))))

/-- One-bit roundtrip through the `getElem` bit list used by `Decode`. -/
theorem holV2w_one (w : BitVec 1) : holV2w 1 [w[0]] = w := holV2w_holW2v w

/-- Six-bit roundtrip through the `getElem` bit list used by `Decode`. -/
theorem holV2w_six (w : BitVec 6) :
    holV2w 6 [w[5], w[4], w[3], w[2], w[1], w[0]] = w := holV2w_holW2v w

/-- `EncodeBitMask` succeeds only when `DecodeBitMasks` recovers the original
immediate (the guard `imm == imm2` of `EncodeBitMask_def`). -/
theorem EncodeBitMask_spec (imm : BitVec 64) (N : BitVec 1) (imms immr : BitVec 6)
    (h : EncodeBitMask imm = some (N, (imms, immr))) :
    ∃ tmask, DecodeBitMasks (TM := 64) (N, (imms, immr, true)) = some (imm, tmask) := by
  cases haux : EncodeBitMaskAux imm with
  | mk e SR =>
  obtain ⟨S, R⟩ := SR
  unfold EncodeBitMask at h
  rw [haux] at h
  simp only at h
  by_cases he : (e == 64) = true
  · rw [ite_eq_left he] at h
    cases hd : DecodeBitMasks (TM := 64)
        (1#1, (BitVec.ofNat 6 (S - 1), (BitVec.ofNat 6 R, true))) with
    | none => simp [hd] at h
    | some p =>
      obtain ⟨imm2, tmask⟩ := p
      simp only [hd] at h
      by_cases hi : imm == imm2
      · rw [ite_eq_left hi] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hN, himms, himmr⟩ := h
        refine ⟨tmask, ?_⟩
        rw [← hN, ← himms, ← himmr, beq_iff_eq.mp hi]
        exact hd
      · rw [ite_eq_right hi] at h
        simp at h
  · rw [ite_eq_right he] at h
    cases hd : DecodeBitMasks (TM := 64)
        (0#1, (~~~(BitVec.ofNat 6 (e * 2 - 1)) ||| BitVec.ofNat 6 (S - 1),
          (BitVec.ofNat 6 R, true))) with
    | none => simp [hd] at h
    | some p =>
      obtain ⟨imm2, tmask⟩ := p
      simp only [hd] at h
      by_cases hi : imm == imm2
      · rw [ite_eq_left hi] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hN, himms, himmr⟩ := h
        refine ⟨tmask, ?_⟩
        rw [← hN, ← himms, ← himmr, beq_iff_eq.mp hi]
        exact hd
      · rw [ite_eq_right hi] at h
        simp at h

/-- `DecodeLogicalOp` inverts `EncodeLogicalOp`. -/
theorem DecodeLogicalOp_EncodeLogicalOp (opc : LogicalOp) (s : Bool) (o : BitVec 2)
    (h : EncodeLogicalOp (opc, s) = some o) : DecodeLogicalOp o = (opc, s) := by
  cases opc <;> cases s <;> simp [EncodeLogicalOp] at h
  all_goals rw [← h]
  all_goals simp [DecodeLogicalOp]

/-- `Encode` of an accepted `LogicalImmediate@64` is the documented word. -/
theorem arm8Encode_logicalImmediate (opc : LogicalOp) (s : Bool) (imm : BitVec 64)
    (rn rd : BitVec 5) (N : BitVec 1) (imms immr : BitVec 6) (opc2 : BitVec 2)
    (hbm : EncodeBitMask imm = some (N, (imms, immr)))
    (hop : EncodeLogicalOp (opc, s) = some opc2) :
    Encode (instruction.Data (Data.«LogicalImmediate@64» (1, opc, s, imm, rn, rd))) =
      MachineCode.ARM8 (arm8LogicalImmediateWord opc2 N imms immr rn rd) := by
  simp only [Encode, e_data, arm8LogicalImmediateWord, hbm, hop]

/-- The rendered `Decode` inverts `arm8LogicalImmediateWord`. -/
theorem arm8Decode_logicalImmediate (opc : LogicalOp) (s : Bool) (imm : BitVec 64)
    (rn rd : BitVec 5) (N : BitVec 1) (imms immr : BitVec 6) (opc2 : BitVec 2)
    (hbm : EncodeBitMask imm = some (N, (imms, immr)))
    (hop : EncodeLogicalOp (opc, s) = some opc2) :
    Decode (arm8LogicalImmediateWord opc2 N imms immr rn rd) =
      instruction.Data (Data.«LogicalImmediate@64» (1, opc, s, imm, rn, rd)) := by
  obtain ⟨tmask, hdbm⟩ := EncodeBitMask_spec imm N imms immr hbm
  have hop' := DecodeLogicalOp_EncodeLogicalOp opc s opc2 hop
  simp only [arm8LogicalImmediateWord, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  simp [holV2w_one, holV2w_two, holV2w_five, holV2w_six, hdbm, hop']

/-- `Run` of the `ORR`/no-flags `LogicalImmediate@64` with `rn = 31` (the
`Const` lowering) writes the immediate to `rd` (or to `SP` for `rd = 31`). -/
theorem arm8Run_logicalImmediate_orr (imm : BitVec 64) (rd : BitVec 5) (s : arm8_state) :
    Run (instruction.Data
        (Data.«LogicalImmediate@64» (1, .LogicalOp_ORR, false, imm, 31, rd))) s =
      if rd == 31 then «write'SP» imm s
      else { s with REG := holUpdate rd imm s.REG } := by
  simp only [Run, «dfn'LogicalImmediate», X, SetTheFlags, «write'X»]
  split <;> simp_all

end Flapjack.Compiler.Encoders.Arm8.L3
