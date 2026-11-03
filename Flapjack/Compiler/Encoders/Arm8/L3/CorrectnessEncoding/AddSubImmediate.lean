import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.LogicalShiftedRegister
import Flapjack.Compiler.Encoders.Arm8.Machine.MaskConverses

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

/-!
# `AddSubImmediate@64`: the word, `Encode`, `Decode` and `Run`

`arm8_ast` lowers `Binop Add`/`Binop Sub` with an immediate operand to
`AddSubImmediate@64 (1, op, false, imm, rn, rd)`.  `Encode` accepts the
immediate only when it fits the low twelve bits or the twelve bits shifted by
twelve; this module records the two words and their semantic facts.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The word emitted for `AddSubImmediate@64` (Flapjack infrastructure: a
readable abbreviation for the rendered `e_data` term). -/
def arm8AddSubImmediateWord (op : Bool) (hi : Bool) (imm12 : BitVec 12)
    (rn rd : BitVec 5) : BitVec 32 :=
  BitVec.setWidth 32 ((1 : BitVec 1) ++
    BitVec.setWidth 31 (holV2w 1 [op] ++
      BitVec.setWidth 30 (holV2w 1 [false] ++
        BitVec.setWidth 29 ((BitVec.ofNat 7 (if hi then 69 else 68)) ++
          BitVec.setWidth 22 (imm12 ++ BitVec.setWidth 10 (rn ++ rd))))))

/-- The two-branch body of the rendered `e_data` for `AddSubImmediate@64`. -/
theorem arm8EData_addSubImmediate (op : Bool) (imm : BitVec 64) (rn rd : BitVec 5) :
    e_data (.«AddSubImmediate@64» (1, op, false, imm, rn, rd)) =
      (if ((imm &&& ~~~(4095 : BitVec 64)) == (0 : BitVec 64)) then
        MachineCode.ARM8 (arm8AddSubImmediateWord op false (holWordExtract 12 11 0 imm) rn rd)
      else if ((imm &&& ~~~(16773120 : BitVec 64)) == (0 : BitVec 64)) then
        MachineCode.ARM8 (arm8AddSubImmediateWord op true (holWordExtract 12 23 12 imm) rn rd)
      else MachineCode.BadCode [BitVec.ofNat 8 65, BitVec.ofNat 8 100, BitVec.ofNat 8 100,
        BitVec.ofNat 8 83, BitVec.ofNat 8 117, BitVec.ofNat 8 98, BitVec.ofNat 8 73,
        BitVec.ofNat 8 109, BitVec.ofNat 8 109, BitVec.ofNat 8 101, BitVec.ofNat 8 100,
        BitVec.ofNat 8 105, BitVec.ofNat 8 97, BitVec.ofNat 8 116, BitVec.ofNat 8 101]) := rfl

/-- `Encode` of an immediate that fits the low twelve bits. -/
theorem arm8Encode_addSubImmediate_low (op : Bool) (imm : BitVec 64) (rn rd : BitVec 5)
    (hlow : imm &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64)) :
    Encode (.Data (.«AddSubImmediate@64» (1, op, false, imm, rn, rd))) =
      MachineCode.ARM8 (arm8AddSubImmediateWord op false (holWordExtract 12 11 0 imm) rn rd) := by
  have hc : ((imm &&& ~~~(4095 : BitVec 64)) == (0 : BitVec 64)) = true := by
    rw [beq_iff_eq]; exact hlow
  rw [show Encode (.Data (.«AddSubImmediate@64» (1, op, false, imm, rn, rd))) =
      e_data (.«AddSubImmediate@64» (1, op, false, imm, rn, rd)) from rfl,
    arm8EData_addSubImmediate, hc]
  rw [if_pos rfl]


/-- `Encode` of an immediate whose twelve bits are shifted by twelve. -/
theorem arm8Encode_addSubImmediate_high (op : Bool) (imm : BitVec 64) (rn rd : BitVec 5)
    (hne : ¬ ((imm &&& ~~~(4095 : BitVec 64)) == (0 : BitVec 64)) = true)
    (hhigh : imm &&& ~~~(16773120 : BitVec 64) = (0 : BitVec 64)) :
    Encode (.Data (.«AddSubImmediate@64» (1, op, false, imm, rn, rd))) =
      MachineCode.ARM8 (arm8AddSubImmediateWord op true (holWordExtract 12 23 12 imm) rn rd) := by
  have hc2 : ((imm &&& ~~~(16773120 : BitVec 64)) == (0 : BitVec 64)) = true := by
    rw [beq_iff_eq]; exact hhigh
  rw [show Encode (.Data (.«AddSubImmediate@64» (1, op, false, imm, rn, rd))) =
      e_data (.«AddSubImmediate@64» (1, op, false, imm, rn, rd)) from rfl,
    arm8EData_addSubImmediate, hc2, if_neg hne]
  rw [if_pos rfl]


/-- Twelve-bit roundtrip through the `getElem` bit list used by `Decode`. -/
theorem holV2w_twelve (w : BitVec 12) :
    holV2w 12 [w[11], w[10], w[9], w[8], w[7], w[6], w[5], w[4], w[3], w[2], w[1], w[0]] = w :=
  holV2w_holW2v w

/-- An immediate that fits the low twelve bits is recovered by truncating to
twelve bits and widening back. -/
theorem arm8AddSubImmediate_low_eq (imm : BitVec 64)
    (hlow : imm &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64)) :
    BitVec.setWidth 64 (holWordExtract 12 11 0 imm) = imm := by
  have heq : imm &&& (4095 : BitVec 64) = imm := and_not_eq_zero_eq imm 4095 hlow
  have hlt : imm.toNat < 4096 := by
    have h := congrArg BitVec.toNat heq
    rw [BitVec.toNat_and] at h
    have h2 : imm.toNat &&& 4095 ≤ 4095 := Nat.and_le_right
    have hle : imm.toNat ≤ 4095 := by rw [← h]; exact h2
    omega
  have hx : (holWordExtract 12 11 0 imm).toNat = imm.toNat := by
    have h1 : holWordExtract 12 11 0 imm = BitVec.setWidth 12 imm := by
      simp only [Flapjack.RiscV.L3.holWordExtract]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
    rw [h1, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hlt]
  rw [← BitVec.ofNat_toNat, hx, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The rendered `Decode` inverts the low-immediate word. -/
theorem arm8Decode_addSubImmediate_low (op : Bool) (imm : BitVec 64) (rn rd : BitVec 5)
    (hlow : imm &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64)) :
    Decode (arm8AddSubImmediateWord op false (holWordExtract 12 11 0 imm) rn rd) =
      instruction.Data (Data.«AddSubImmediate@64» (1, op, false, imm, rn, rd)) := by
  have himm := arm8AddSubImmediate_low_eq imm hlow
  simp only [arm8AddSubImmediateWord, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  cases op <;>
    simp [holV2w_two_zero, holV2w_five, holV2w_twelve,
      arm8HolV2w_one_false, arm8HolV2w_one_true, himm]


/-- The two-bit list `false, true` is the one word (bit-list helper). -/
theorem arm8HolV2w_two_one : holV2w 2 [false, true] = (1 : BitVec 2) := by decide

/-- A word killed by the shifted mask is a multiple of `4096` below `2 ^ 24`, so
it is `m <<< 12` for the twelve-bit value the shifted encoding needs. -/
theorem arm8AddSubImmediate_shifted (w : BitVec 64) (hmod : w.toNat % 4096 = 0)
    (hlt : w.toNat < 2 ^ 24) :
    BitVec.ofNat 64 (((w >>> 12).toNat % 4096) <<< 12) = w := by
  have hshift : (w >>> 12).toNat = w.toNat / 4096 := by
    rw [show (w >>> 12).toNat = w.toNat >>> 12 from BitVec.toNat_ushiftRight w 12,
      Nat.shiftRight_eq_div_pow]
  have hquo : w.toNat / 4096 % 4096 = w.toNat / 4096 := by
    apply Nat.mod_eq_of_lt
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, hshift, hquo, Nat.shiftLeft_eq]
  have hdvd : 4096 ∣ w.toNat := Nat.dvd_of_mod_eq_zero hmod
  rw [show (2 : Nat) ^ 12 = 4096 from rfl, Nat.div_mul_cancel hdvd]
  exact Nat.mod_eq_of_lt w.isLt

/-- An immediate whose twelve bits are shifted by twelve is recovered by
extracting those bits and shifting them back. -/
theorem arm8AddSubImmediate_high_eq (imm : BitVec 64)
    (hhigh : imm &&& ~~~(16773120 : BitVec 64) = (0 : BitVec 64)) :
    BitVec.setWidth 64 (holWordExtract 12 23 12 imm) <<< 12 = imm := by
  have hmod : imm.toNat % 4096 = 0 := and_not_fff000_eq_zero_toNat_mod hhigh
  have hlt : imm.toNat < 2 ^ 24 := and_not_fff000_eq_zero_toNat_lt hhigh
  have hx : holWordExtract 12 23 12 imm = BitVec.setWidth 12 (imm >>> 12) := by
    simp only [Flapjack.RiscV.L3.holWordExtract]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
  have hsh : (BitVec.ofNat 64 ((imm >>> 12).toNat % 4096)) <<< 12
      = BitVec.ofNat 64 (((imm >>> 12).toNat % 4096) <<< 12) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_mod]
  rw [hx, ← BitVec.ofNat_toNat, BitVec.toNat_setWidth, hsh]
  exact arm8AddSubImmediate_shifted imm hmod hlt

/-- The rendered `Decode` inverts the shifted-immediate word. -/
theorem arm8Decode_addSubImmediate_high (op : Bool) (imm : BitVec 64) (rn rd : BitVec 5)
    (hhigh : imm &&& ~~~(16773120 : BitVec 64) = (0 : BitVec 64)) :
    Decode (arm8AddSubImmediateWord op true (holWordExtract 12 23 12 imm) rn rd) =
      instruction.Data (Data.«AddSubImmediate@64» (1, op, false, imm, rn, rd)) := by
  have himm := arm8AddSubImmediate_high_eq imm hhigh
  simp only [arm8AddSubImmediateWord, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  cases op <;>
    simp [arm8HolV2w_two_one, holV2w_five, holV2w_twelve,
      arm8HolV2w_one_false, arm8HolV2w_one_true] <;>
    exact himm


/-- `Run` of a flag-preserving `AddSubImmediate@64` writes the sum or difference
with the immediate to `rd` (for `rd ≠ 31`). -/
theorem arm8Run_addSubImmediate (op : Bool) (imm : BitVec 64) (rn rd : BitVec 5)
    (st : arm8_state) (hrn : rn ≠ 31) (hrd : rd ≠ 31) :
    Run (instruction.Data (Data.«AddSubImmediate@64» (1, op, false, imm, rn, rd))) st =
      write'X ((if op then X (TN := 64) rn st - imm else X (TN := 64) rn st + imm), rd) st := by
  have hrn' : (rn == (31 : BitVec 5)) = false := by
    cases h : (rn == (31 : BitVec 5))
    · rfl
    · exact absurd (by simpa using h) hrn
  have hrd' : (rd == (31 : BitVec 5)) = false := by
    cases h : (rd == (31 : BitVec 5))
    · rfl
    · exact absurd (by simpa using h) hrd
  simp only [Run, «dfn'AddSubImmediate», SetTheFlags, Bool.false_eq_true, if_false]
  cases op
  · simp_all [arm8AddWithCarry_add]
  · simp_all [arm8AddWithCarry_sub]

/-- The `binop` `add`/`sub` immediate constructor of
`encoder_correct arm8TargetL3`, lowered to `AddSubImmediate@64`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_binop_addsub_imm (op : Bool) (bop : HolBinop)
    (hbop : bop = if op then .sub else .add) (destination source : Nat) (value : BitVec 64)
    (hvalid : value &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64) ∨
      value &&& ~~~(16773120 : BitVec 64) = (0 : BitVec 64))
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.arith (.binop bop destination source (.imm value)))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.arith (.binop bop destination source (.imm value)))) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  obtain ⟨hok, hpc, hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change ms.PC = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.MEM a = s1.mem a at hmem
  change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
    ms.REG (BitVec.ofNat 5 k) = s1.regs k at hreg
  have hokinst : asmOkExact (.inst (.arith (.binop bop destination source (.imm value))))
      arm8ConfigL3 = true := hs.2.2.2.2.2.2
  have hregok : (asmRegOkExact destination arm8ConfigL3 = true ∧
      asmRegOkExact source arm8ConfigL3 = true) ∧
      asmRegImmOkExact (.inl bop) (.imm value) arm8ConfigL3 = true := by
    simpa [asmOkExact, asmInstOkExact, asmArithOkExact, arm8ConfigL3,
      Bool.and_eq_true] using hokinst
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hregok.1.1
  obtain ⟨hslt, hsav, hs31⟩ := regOk_of_asmL3 hregok.1.2
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC
      (arm8Enc (.inst (.arith (.binop bop destination source (.imm value))))) ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hdom n hn)).symm⟩
  have hast : arm8Ast (.inst (.arith (.binop bop destination source (.imm value)))) =
      [.Data (.«AddSubImmediate@64»
        (1, op, false, value, BitVec.ofNat 5 source, BitVec.ofNat 5 destination))] := by
    cases op <;> simp [arm8Ast, hbop]
  have henc : arm8Enc (.inst (.arith (.binop bop destination source (.imm value)))) =
      arm8Encode (.Data (.«AddSubImmediate@64»
        (1, op, false, value, BitVec.ofNat 5 source, BitVec.ofNat 5 destination))) := by
    rw [arm8Enc, hast]
    simp
  have hlen : (arm8Enc (.inst (.arith (.binop bop destination source (.imm value))))).length = 4 := by
    rw [henc]; exact arm8Encode_length _
  have hworddec : ∃ (w : BitVec 32),
      Encode (.Data (.«AddSubImmediate@64»
        (1, op, false, value, BitVec.ofNat 5 source, BitVec.ofNat 5 destination))) =
        MachineCode.ARM8 w ∧
      Decode w = instruction.Data (Data.«AddSubImmediate@64»
        (1, op, false, value, BitVec.ofNat 5 source, BitVec.ofNat 5 destination)) := by
    by_cases hlow : value &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64)
    · exact ⟨_, arm8Encode_addSubImmediate_low op value _ _ hlow,
        arm8Decode_addSubImmediate_low op value _ _ hlow⟩
    · have hhigh : value &&& ~~~(16773120 : BitVec 64) = (0 : BitVec 64) := by
        rcases hvalid with hv | hv
        · exact absurd hv hlow
        · exact hv
      have hne : ¬ ((value &&& ~~~(4095 : BitVec 64)) == (0 : BitVec 64)) = true := by
        intro hb'
        exact hlow (beq_iff_eq.mp hb')
      exact ⟨_, arm8Encode_addSubImmediate_high op value _ _ hne hhigh,
        arm8Decode_addSubImmediate_high op value _ _ hhigh⟩
  obtain ⟨w, hword, hdec⟩ := hworddec
  have h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w >>> 0).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 0 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode] at hh
    rw [hword] at hh
    simp at hh
    simpa using hh
  have h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w >>> 8).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 1 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode] at hh
    rw [hword] at hh
    simp at hh
    simpa using hh
  have h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w >>> 16).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 2 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode] at hh
    rw [hword] at hh
    simp at hh
    simpa using hh
  have h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w >>> 24).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 3 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode] at hh
    rw [hword] at hh
    simp at hh
    simpa using hh
  let v : BitVec 64 := if op then ms.REG (BitVec.ofNat 5 source) - value
    else ms.REG (BitVec.ofNat 5 source) + value
  have hsne : BitVec.ofNat 5 source ≠ 31#5 := by
    intro hh
    have hto := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat] at hto
    have h31 : (31#5).toNat = 31 := by decide
    rw [h31] at hto
    have hs32 : source % 2 ^ 5 = source := Nat.mod_eq_of_lt (by omega)
    omega
  have hrdne : BitVec.ofNat 5 destination ≠ 31#5 := by
    intro hh
    have hto := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat] at hto
    have h31 : (31#5).toNat = 31 := by decide
    rw [h31] at hto
    have hd32 : destination % 2 ^ 5 = destination := Nat.mod_eq_of_lt (by omega)
    omega
  have hbr : (Run (instruction.Data (Data.«AddSubImmediate@64»
      (1, op, false, value, BitVec.ofNat 5 source, BitVec.ofNat 5 destination)))
      { ms with branch_hint := none }).branch_hint = none := by
    rw [arm8Run_addSubImmediate _ _ _ _ _ hsne hrdne]
    simp only [«write'X»]
    split <;> rfl
  have hexc : (Run (instruction.Data (Data.«AddSubImmediate@64»
      (1, op, false, value, BitVec.ofNat 5 source, BitVec.ofNat 5 destination)))
      { ms with branch_hint := none }).exception = exception.NoException := by
    rw [arm8Run_addSubImmediate _ _ _ _ _ hsne hrdne]
    simp only [«write'X»]
    split <;> simpa using hexc0
  have hn := arm8Next_word ms w
    (instruction.Data (Data.«AddSubImmediate@64»
      (1, op, false, value, BitVec.ofNat 5 source, BitVec.ofNat 5 destination)))
    hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  have hrun : Run (instruction.Data (Data.«AddSubImmediate@64»
      (1, op, false, value, BitVec.ofNat 5 source, BitVec.ofNat 5 destination)))
      { ms with branch_hint := none } =
      { ms with branch_hint := none, REG := holUpdate (BitVec.ofNat 5 destination) v ms.REG } := by
    rw [arm8Run_addSubImmediate _ _ _ _ _ hsne hrdne]
    rw [arm8WriteX_of_valid _ _ hd31 hdlt]
    cases op
    · simp [v, holUpdate, arm8X_of_valid _ hs31 hslt]
    · simp [v, holUpdate, arm8X_of_valid _ hs31 hslt]
  have hnext : arm8Next ms = { ms with branch_hint := none, REG := holUpdate (BitVec.ofNat 5 destination) v ms.REG, PC := ms.PC + 4 } := by
    unfold arm8Next
    rw [hn, hrun]
    rfl
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  rw [hlen] at hupd
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 4 := by
    rw [← hupd]; simp [asmUpd, instUpd, arithUpd, updPc]
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    intro x; rw [← hupd]; simp [asmUpd, instUpd, arithUpd, binopUpd, updReg, updPc]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]; simp [asmUpd, instUpd, arithUpd, binopUpd, updReg, updPc]
  have hs2regs : ∀ k, s2.regs k = if k = destination then v else s1.regs k := by
    intro k
    rw [← hupd]
    cases op
    · simp [asmUpd, instUpd, arithUpd, binopUpd, updReg, updPc, v, hbop,
        Flapjack.Compiler.Encoders.AsmSem.readReg, Flapjack.Compiler.Encoders.AsmSem.regImm,
        hreg source ⟨hslt, hsav⟩]
    · simp [asmUpd, instUpd, arithUpd, binopUpd, updReg, updPc, v, hbop,
        Flapjack.Compiler.Encoders.AsmSem.readReg, Flapjack.Compiler.Encoders.AsmSem.regImm,
        hreg source ⟨hslt, hsav⟩]
  refine asmCaseOne (.arith (.binop bop destination source (.imm value))) destination v
    _ s1 s2 ms ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ hnext ?_ ?_ ?_ ?_ ?_ hs2pc hs2mem hs2dom hs2regs
  · rfl
  · intro x; rfl
  · intro k hk hkne
    show (if (BitVec.ofNat 5 destination) = (BitVec.ofNat 5 k) then v
      else ms.REG (BitVec.ofNat 5 k)) = ms.REG (BitVec.ofNat 5 k)
    rw [if_neg]
    intro hh
    apply hkne
    have := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    have hd32 : destination % 2 ^ 5 = destination := Nat.mod_eq_of_lt (by omega)
    have hk32 : k % 2 ^ 5 = k := Nat.mod_eq_of_lt (by omega)
    omega
  · show (if (BitVec.ofNat 5 destination) = (BitVec.ofNat 5 destination) then v
      else ms.REG (BitVec.ofNat 5 destination)) = v
    rw [if_pos rfl]
  · rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, ?_⟩
    have h4 : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
    have hal4 : holAligned 2 (ms.PC + 4) = true := by
      rw [(alignedAddSub 2 ms.PC 4 h4).1, halign]
    change holAligned 2 (ms.PC + 4) = true
    exact hal4

/-- The set-flags word for `AddSubImmediate@64` (`S := T`, the compare shape
`arm8_ast` emits for the ordering `JumpCmp` forms). -/
def arm8AddSubImmediateWordS (op : Bool) (hi : Bool) (imm12 : BitVec 12)
    (rn rd : BitVec 5) : BitVec 32 :=
  BitVec.setWidth 32 ((1 : BitVec 1) ++
    BitVec.setWidth 31 (holV2w 1 [op] ++
      BitVec.setWidth 30 (holV2w 1 [true] ++
        BitVec.setWidth 29 ((BitVec.ofNat 7 (if hi then 69 else 68)) ++
          BitVec.setWidth 22 (imm12 ++ BitVec.setWidth 10 (rn ++ rd))))))

/-- The two-branch body of the rendered `e_data` for the set-flags
`AddSubImmediate@64`. -/
theorem arm8EData_addSubImmediateS (op : Bool) (imm : BitVec 64) (rn rd : BitVec 5) :
    e_data (.«AddSubImmediate@64» (1, op, true, imm, rn, rd)) =
      (if ((imm &&& ~~~(4095 : BitVec 64)) == (0 : BitVec 64)) then
        MachineCode.ARM8 (arm8AddSubImmediateWordS op false (holWordExtract 12 11 0 imm) rn rd)
      else if ((imm &&& ~~~(16773120 : BitVec 64)) == (0 : BitVec 64)) then
        MachineCode.ARM8 (arm8AddSubImmediateWordS op true (holWordExtract 12 23 12 imm) rn rd)
      else MachineCode.BadCode [BitVec.ofNat 8 65, BitVec.ofNat 8 100, BitVec.ofNat 8 100,
        BitVec.ofNat 8 83, BitVec.ofNat 8 117, BitVec.ofNat 8 98, BitVec.ofNat 8 73,
        BitVec.ofNat 8 109, BitVec.ofNat 8 109, BitVec.ofNat 8 101, BitVec.ofNat 8 100,
        BitVec.ofNat 8 105, BitVec.ofNat 8 97, BitVec.ofNat 8 116, BitVec.ofNat 8 101]) := rfl

/-- `Encode` of a set-flags immediate that fits the low twelve bits. -/
theorem arm8Encode_addSubImmediateS_low (op : Bool) (imm : BitVec 64) (rn rd : BitVec 5)
    (hlow : imm &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64)) :
    Encode (.Data (.«AddSubImmediate@64» (1, op, true, imm, rn, rd))) =
      MachineCode.ARM8 (arm8AddSubImmediateWordS op false (holWordExtract 12 11 0 imm) rn rd) := by
  have hc : ((imm &&& ~~~(4095 : BitVec 64)) == (0 : BitVec 64)) = true := by
    rw [beq_iff_eq]; exact hlow
  rw [show Encode (.Data (.«AddSubImmediate@64» (1, op, true, imm, rn, rd))) =
      e_data (.«AddSubImmediate@64» (1, op, true, imm, rn, rd)) from rfl,
    arm8EData_addSubImmediateS, hc]
  rw [if_pos rfl]

/-- `Encode` of a set-flags immediate whose twelve bits are shifted by twelve. -/
theorem arm8Encode_addSubImmediateS_high (op : Bool) (imm : BitVec 64) (rn rd : BitVec 5)
    (hne : ¬ ((imm &&& ~~~(4095 : BitVec 64)) == (0 : BitVec 64)) = true)
    (hhigh : imm &&& ~~~(16773120 : BitVec 64) = (0 : BitVec 64)) :
    Encode (.Data (.«AddSubImmediate@64» (1, op, true, imm, rn, rd))) =
      MachineCode.ARM8 (arm8AddSubImmediateWordS op true (holWordExtract 12 23 12 imm) rn rd) := by
  have hc2 : ((imm &&& ~~~(16773120 : BitVec 64)) == (0 : BitVec 64)) = true := by
    rw [beq_iff_eq]; exact hhigh
  rw [show Encode (.Data (.«AddSubImmediate@64» (1, op, true, imm, rn, rd))) =
      e_data (.«AddSubImmediate@64» (1, op, true, imm, rn, rd)) from rfl,
    arm8EData_addSubImmediateS, hc2, if_neg hne]
  rw [if_pos rfl]

/-- The rendered `Decode` inverts the set-flags low-immediate word. -/
theorem arm8Decode_addSubImmediateS_low (op : Bool) (imm : BitVec 64) (rn rd : BitVec 5)
    (hlow : imm &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64)) :
    Decode (arm8AddSubImmediateWordS op false (holWordExtract 12 11 0 imm) rn rd) =
      instruction.Data (Data.«AddSubImmediate@64» (1, op, true, imm, rn, rd)) := by
  have himm := arm8AddSubImmediate_low_eq imm hlow
  simp only [arm8AddSubImmediateWordS, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  cases op <;>
    simp [holV2w_two_zero, holV2w_five, holV2w_twelve,
      arm8HolV2w_one_false, arm8HolV2w_one_true, himm]

/-- The rendered `Decode` inverts the set-flags high-immediate word. -/
theorem arm8Decode_addSubImmediateS_high (op : Bool) (imm : BitVec 64) (rn rd : BitVec 5)
    (hhigh : imm &&& ~~~(16773120 : BitVec 64) = (0 : BitVec 64)) :
    Decode (arm8AddSubImmediateWordS op true (holWordExtract 12 23 12 imm) rn rd) =
      instruction.Data (Data.«AddSubImmediate@64» (1, op, true, imm, rn, rd)) := by
  have himm := arm8AddSubImmediate_high_eq imm hhigh
  simp only [arm8AddSubImmediateWordS, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  cases op <;>
    simp [arm8HolV2w_two_one, holV2w_five, holV2w_twelve,
      arm8HolV2w_one_false, arm8HolV2w_one_true] <;>
    exact himm

end Flapjack.Compiler.Encoders.Arm8.L3
