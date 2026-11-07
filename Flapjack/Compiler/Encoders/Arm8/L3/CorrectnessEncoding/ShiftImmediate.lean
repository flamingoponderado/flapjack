import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Shift

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

/-!
# `ExtractRegister@64`: the `.ror` immediate form of `shift`

`arm8_ast` lowers `Arith (Shift .ror d s (Imm v))` to the single instruction
`ExtractRegister@64 (1, v, s, s, d)`, whose semantics is the rotate right of
`s` by `v` (`holShiftr` of the doubled bit vector).  This module records the
emitted word, its `Encode`/`Decode` inverse, the `Run` semantics, and the
corresponding case of `encoder_correct arm8TargetL3`.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The word emitted for `ExtractRegister@64`: HOL's `e_data` term
`0b10010011110 ++ Rm ++ imms ++ Rn ++ Rd` (Flapjack infrastructure: a readable
abbreviation for a mechanically rendered term). -/
def arm8ExtractWord (imms : BitVec 6) (rm rn rd : BitVec 5) : BitVec 32 :=
  BitVec.setWidth 32 ((BitVec.ofNat 11 1182) ++
    BitVec.setWidth 21 (rm ++
      BitVec.setWidth 16 (imms ++
        BitVec.setWidth 10 (rn ++ rd))))

/-- `e_data` of `ExtractRegister@64` is the extract word (Flapjack
infrastructure; no separately named HOL declaration). -/
theorem arm8EData_extract (imms : BitVec 6) (rm rn rd : BitVec 5) :
    e_data (.«ExtractRegister@64» ((1 : BitVec 64), (imms, (rm, (rn, rd))))) =
      MachineCode.ARM8 (arm8ExtractWord imms rm rn rd) := by
  rfl

/-- `Encode` of `ExtractRegister@64` is the extract word (Flapjack
infrastructure; no separately named HOL declaration). -/
theorem arm8Encode_extract (imms : BitVec 6) (rm rn rd : BitVec 5) :
    Encode (.Data (.«ExtractRegister@64» ((1 : BitVec 64), (imms, (rm, (rn, rd)))))) =
      MachineCode.ARM8 (arm8ExtractWord imms rm rn rd) := by
  simp only [Encode, arm8EData_extract]

/-- The rendered `Decode` inverts `arm8ExtractWord`. -/
theorem arm8Decode_extract (imms : BitVec 6) (rm rn rd : BitVec 5) :
    Decode (arm8ExtractWord imms rm rn rd) =
      instruction.Data (Data.«ExtractRegister@64»
        ((1 : BitVec 64), (imms, (rm, (rn, rd))))) := by
  simp only [arm8ExtractWord, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  simp [holV2w_one_true, holV2w_six, holV2w_five]

/-- The `getD` of `holW2v` is the corresponding bit of the word. -/
theorem holW2v_getD (v : BitVec 64) {j : Nat} (hj : j < 64) :
    (holW2v v).getD j false = v.getLsbD (63 - j) := by
  simp [holW2v, List.getD_eq_getElem?_getD, hj]

/-- `holW2v` of a 64-bit word has length 64. -/
theorem holW2v_length (v : BitVec 64) : (holW2v v).length = 64 := by
  simp [holW2v]

/-- `ExtractRegister`'s doubled-bit-vector shift is the rotate right. -/
theorem holV2w_extract_ror (v : BitVec 64) (k : Nat) (hk : k < 64) :
    holV2w 64 (holShiftr (holW2v v ++ holW2v v) k) = v.rotateRight k := by
  have hlen : (holW2v v).length = 64 := holW2v_length v
  have hlen128 : (holW2v v ++ holW2v v).length = 128 := by
    simp [hlen]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [holV2w, Flapjack.RiscV.L3.holV2w, Flapjack.getLsbD_holFcpWord,
    BitVec.getLsbD_rotateRight]
  have htake : (holShiftr (holW2v v ++ holW2v v) k).length = 128 - k := by
    simp [holShiftr, hlen128]
  have hi' : i < 128 - k := by omega
  rw [htake]
  simp only [decide_eq_true hi', Bool.true_and, holShiftr, hlen128]
  have hj : 128 - k - 1 - i < 128 - k := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hj, List.getElem?_append]
  rw [Nat.mod_eq_of_lt hk]
  by_cases hin : i < 64 - k
  · rw [ite_eq_left hin]
    have hj2 : ¬ 128 - k - 1 - i < (holW2v v).length := by rw [hlen]; omega
    have hidx : 128 - k - 1 - i - (holW2v v).length = 63 - k - i := by rw [hlen]; omega
    have hlt : 63 - k - i < 64 := by omega
    simp only [hj2, ite_false, hidx, decide_eq_true hi, Bool.true_and]
    rw [← List.getD_eq_getElem?_getD, holW2v_getD v hlt]
    congr 1
    omega
  · rw [ite_eq_right hin]
    have hj2 : 128 - k - 1 - i < (holW2v v).length := by rw [hlen]; omega
    have hlt : 128 - k - 1 - i < 64 := by omega
    simp only [hj2, ite_true, decide_eq_true hi, Bool.true_and]
    rw [← List.getD_eq_getElem?_getD, holW2v_getD v hlt]
    congr 1
    omega

/-- `Run` of `ExtractRegister@64`: rotate `Rn` right by `imms` and write the
result to `Rd`. -/
theorem arm8Run_extract (imms : BitVec 6) (rm rn rd : BitVec 5) (st : arm8_state) :
    Run (instruction.Data (Data.«ExtractRegister@64» ((1 : BitVec 64), (imms, (rm, (rn, rd)))))) st =
      «write'X» (holV2w 64 (holShiftr (holW2v (X (TN := 64) rn st) ++
        holW2v (X (TN := 64) rm st)) imms.toNat), rd) st := by
  simp only [Run, «dfn'ExtractRegister»]



/-! ## The `.ror` immediate constructor -/

/-- The `.ror` immediate constructor of `encoder_correct arm8TargetL3`, lowered
to the single instruction `ExtractRegister@64`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_shift_ror_imm (destination source : Nat) (value : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.arith (.shift .ror destination source (.imm value)))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.arith (.shift .ror destination source (.imm value)))) s1 s2 ms := by
  have hs := h.1
  have hregok : (asmRegOkExact destination arm8ConfigL3 = true ∧
      asmRegOkExact source arm8ConfigL3 = true) ∧
      ((!(value == 0) || Flapjack.Shift.ror == Flapjack.Shift.lsl) = true ∧
        value.toNat < 64) := by
    have hk := hs.2.2.2.2.2.2
    simpa [asmOkExact, asmInstOkExact, asmArithOkExact, arm8ConfigL3,
      Bool.and_eq_true] using hk
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hregok.1.1
  obtain ⟨hslt, hsav, hs31⟩ := regOk_of_asmL3 hregok.1.2
  have hlt : value.toNat < 64 := hregok.2.2
  have hast : arm8Ast (.inst (.arith (.shift .ror destination source (.imm value)))) =
      [.Data (.«ExtractRegister@64» (1, BitVec.ofNat 6 value.toNat, BitVec.ofNat 5 source,
        BitVec.ofNat 5 source, BitVec.ofNat 5 destination))] := by
    simp [arm8Ast]
  have henc : arm8Enc (.inst (.arith (.shift .ror destination source (.imm value)))) =
      arm8Encode (.Data (.«ExtractRegister@64» (1, BitVec.ofNat 6 value.toNat,
        BitVec.ofNat 5 source, BitVec.ofNat 5 source, BitVec.ofNat 5 destination))) := by
    rw [arm8Enc, hast]
    simp
  let w : BitVec 32 := arm8ExtractWord (BitVec.ofNat 6 value.toNat) (BitVec.ofNat 5 source)
    (BitVec.ofNat 5 source) (BitVec.ofNat 5 destination)
  have hdec : Decode w = instruction.Data (Data.«ExtractRegister@64»
      ((1 : BitVec 64), (BitVec.ofNat 6 value.toNat, (BitVec.ofNat 5 source,
        (BitVec.ofNat 5 source, BitVec.ofNat 5 destination))))) :=
    arm8Decode_extract _ _ _ _
  let v : BitVec 64 := wordShift .ror (s1.regs source) value.toNat
  have himms : (BitVec.ofNat 6 value.toNat).toNat = value.toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  refine arm8RegCaseOne _ destination v s1 s2 ms h (by omega) _ _ _ henc (by rw [arm8Encode_extract]) hdec ?_ ?_
  · intro hreg
    rw [arm8Run_extract, arm8WriteX_of_valid _ _ hd31 hdlt]
    have hX : X (TN := 64) (BitVec.ofNat 5 source) { ms with branch_hint := none } =
        s1.regs source := by
      rw [arm8X_of_valid _ hs31 hslt]
      exact hreg source ⟨hslt, hsav⟩
    rw [himms, holV2w_extract_ror _ value.toNat hlt]
    simp [hX, v, holUpdate, wordShift]
  · intro hreg p
    refine ⟨?_, fun x => ?_, ?_, fun k => ?_⟩
    · simp [asmUpd, instUpd, arithUpd, updPc]
    · simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc]
    · simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc]
    · simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc, v,
        Flapjack.Compiler.Encoders.AsmSem.readReg, Flapjack.Compiler.Encoders.AsmSem.regImm]

end Flapjack.Compiler.Encoders.Arm8.L3
