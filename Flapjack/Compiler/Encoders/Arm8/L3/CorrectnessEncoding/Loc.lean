import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Const
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.MoveWide
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Simulate

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-!
# The `Loc` constructor of `encoder_correct arm8TargetL3`

`arm8_ast` lowers `Loc r i` to a single `Address` instruction when `i` is in the
signed 20-bit range, and to a six-instruction sequence otherwise.  This module
records the `Address` instruction facts: the word, its `Encode`/`Decode`
inverse and its `Run` semantics.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The word emitted for `Address` with page `false`: HOL's `e_data` term
`0 ++ immlo ++ 10000 ++ immhi ++ Rd`. -/
def arm8AddressWord (imm : BitVec 64) (rd : BitVec 5) : BitVec 32 :=
  BitVec.setWidth 32 ((BitVec.ofNat 1 0) ++
    BitVec.setWidth 31 (holWordExtract 2 1 0 imm ++
      BitVec.setWidth 29 ((BitVec.ofNat 5 16) ++
        BitVec.setWidth 24 (holWordExtract 19 20 2 imm ++ rd))))

/-- Bit `i` of `x % 4` is bit `i` of `x` for `i < 2`. -/
theorem arm8TestBit_mod_four (x i : Nat) (hi : i < 2) : (x % 4).testBit i = x.testBit i := by
  have h := Nat.testBit_mod_two_pow x 2 i
  rw [show (2 : Nat) ^ 2 = 4 from rfl] at h
  rw [h]
  simp [hi]

/-- The bits 20:2 of a word sit at positions `i - 2` after a two-bit shift. -/
theorem arm8TestBit_shift_mod (x i : Nat) (h2 : 2 ≤ i) (hi : i < 21) :
    (x >>> 2 % 524288).testBit (i - 2) = x.testBit i := by
  have h := Nat.testBit_mod_two_pow (x >>> 2) 19 (i - 2)
  rw [show (2 : Nat) ^ 19 = 524288 from rfl] at h
  rw [h]
  rw [Nat.testBit_shiftRight]
  have h3 : 2 + (i - 2) = i := by omega
  rw [h3]
  simp [show i - 2 < 19 from by omega]

/-- The 21-bit address immediate reassembles to the low 21 bits of the
offset. -/
theorem arm8AddressBits (imm : BitVec 64) :
    (holWordExtract 19 20 2 imm ++ holWordExtract 2 1 0 imm) = BitVec.setWidth 21 imm := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [holWordExtract, Flapjack.RiscV.L3.holWordExtract, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat]
  norm_num
  by_cases h2 : i < 2
  · rw [ite_eq_left h2, arm8TestBit_mod_four _ _ h2]
    simp [BitVec.getLsbD, h2, hi]
    omega
  · have h19 : i - 2 < 19 := by omega
    have h64 : i - 2 < 64 := by omega
    rw [ite_eq_right h2, arm8TestBit_shift_mod _ _ (by omega) (by omega)]
    simp [BitVec.getLsbD, h19, h64, hi]

/-- The signed value of the low 21 bits of an offset in the signed 20-bit
`Loc` range is the offset itself. -/
theorem arm8SignExtend21 (imm : BitVec 64)
    (hlo : -(2 ^ 19 : Int) ≤ imm.toInt) (hhi : imm.toInt ≤ 2 ^ 19 - 1) :
    BitVec.signExtend 64 (BitVec.setWidth 21 imm) = imm := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend, BitVec.toInt_setWidth, BitVec.toInt_eq_toNat_bmod]
  norm_num
  have hdvd64 : ((2 ^ 64 : ℕ) : ℤ) ∣ imm.toInt - ((imm.toNat : ℕ) : ℤ) := by
    rw [BitVec.toInt_eq_toNat_bmod]
    exact ((Int.bmod_eq_iff (by norm_num : 0 < 2 ^ 64)).mp rfl).2.2
  have hdvd21 : ((2 ^ 21 : ℕ) : ℤ) ∣ imm.toInt - ((imm.toNat : ℕ) : ℤ) := by
    obtain ⟨c, hc⟩ := hdvd64
    refine ⟨c * (2 ^ 43 : ℤ), ?_⟩
    rw [hc]
    push_cast
    omega
  have hb21 : 0 < (2 ^ 21 : ℕ) := by norm_num
  rw [← BitVec.toInt_eq_toNat_bmod]
  refine (Int.bmod_eq_iff hb21).mpr ⟨?_, ?_, hdvd21⟩
  · push_cast; omega
  · push_cast; omega

/-- The `Address` instruction's 21-bit immediate reassembles to the offset
when the offset is in the signed 20-bit `Loc` range. -/
theorem arm8AddressRoundtrip (imm : BitVec 64)
    (hlo : -(2 ^ 19 : Int) ≤ imm.toInt) (hhi : imm.toInt ≤ 2 ^ 19 - 1) :
    BitVec.signExtend 64 (BitVec.setWidth 21
      (holWordExtract 19 20 2 imm ++ holWordExtract 2 1 0 imm)) = imm := by
  rw [arm8AddressBits, BitVec.setWidth_setWidth_of_le _ (by norm_num)]
  exact arm8SignExtend21 imm hlo hhi

/-- `Encode` of an in-range `Address` is the address word. -/
theorem arm8Encode_address (imm : BitVec 64) (rd : BitVec 5)
    (h : BitVec.signExtend 64 (BitVec.setWidth 21
      (holWordExtract 19 20 2 imm ++ holWordExtract 2 1 0 imm)) = imm) :
    Encode (.Address (false, (imm, rd))) = MachineCode.ARM8 (arm8AddressWord imm rd) := by
  simp only [Encode, arm8AddressWord, Bool.false_eq_true, ite_false]
  rw [h]
  simp

/-- The rendered `Decode` inverts the address word. -/
theorem arm8Decode_address (imm : BitVec 64) (rd : BitVec 5)
    (h : BitVec.signExtend 64 (BitVec.setWidth 21
      (holWordExtract 19 20 2 imm ++ holWordExtract 2 1 0 imm)) = imm) :
    Decode (arm8AddressWord imm rd) = .Address (false, (imm, rd)) := by
  simp only [arm8AddressWord, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  simp [holV2w_nineteen, holV2w_two, holV2w_one_false]
  exact ⟨by simpa [BitVec.setWidth_eq] using h, holV2w_five rd⟩

/-- `Run` of `Address` with page `false` writes `PC + imm` to `Rd`. -/
theorem arm8Run_address (imm : BitVec 64) (rd : BitVec 5) (st : arm8_state) :
    Run (.Address (false, (imm, rd))) st = «write'X» ((st.PC + imm), rd) st := by
  simp only [Run, «dfn'Address», Bool.false_eq_true, ite_false]

/-- The offset reassembles from the address word's 21-bit immediate. -/
theorem arm8AddressRoundtripBits (imm : BitVec 64) :
    BitVec.signExtend 64 (BitVec.setWidth 21
      (holWordExtract 19 20 2 imm ++ holWordExtract 2 1 0 imm)) =
      BitVec.signExtend 64 (BitVec.setWidth 21 imm) := by
  rw [arm8AddressBits, BitVec.setWidth_setWidth_of_le _ (by norm_num)]

/-- One `arm8Next` step on the address word writes `PC + imm` to `Rd` and
advances `PC` by four. -/
theorem arm8Next_address (ms : arm8_state) (imm : BitVec 64) (rd : Nat)
    (hrd : rd ≠ 31) (hlt : rd < 32)
    (hround : BitVec.signExtend 64 (BitVec.setWidth 21
      (holWordExtract 19 20 2 imm ++ holWordExtract 2 1 0 imm)) = imm)
    (hexc0 : ms.exception = exception.NoException)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((arm8AddressWord imm (BitVec.ofNat 5 rd) >>> 0).toNat))
    (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((arm8AddressWord imm (BitVec.ofNat 5 rd) >>> 8).toNat))
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((arm8AddressWord imm (BitVec.ofNat 5 rd) >>> 16).toNat))
    (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((arm8AddressWord imm (BitVec.ofNat 5 rd) >>> 24).toNat))
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    arm8Next ms =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 rd) (ms.PC + imm) ms.REG,
        PC := ms.PC + 4 } := by
  let i : instruction := .Address (false, (imm, BitVec.ofNat 5 rd))
  have hdec : Decode (arm8AddressWord imm (BitVec.ofNat 5 rd)) = i := by
    dsimp only [i]
    exact arm8Decode_address imm _ hround
  have hrun : Run i { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 rd) (ms.PC + imm) ms.REG } := by
    dsimp only [i]
    rw [arm8Run_address]
    rw [arm8WriteX_of_valid _ _ hrd hlt]
  refine arm8Next_eq ms _ _ _ hdec ?_ rfl hexc0 h0 h1 h2 h3 hal he0 hel
  rw [hrun]

/-- The four encoded bytes of the address word. -/
theorem arm8EncodeBytes_address (imm : BitVec 64) (rd : BitVec 5)
    (h : BitVec.signExtend 64 (BitVec.setWidth 21
      (holWordExtract 19 20 2 imm ++ holWordExtract 2 1 0 imm)) = imm) :
    arm8Encode (.Address (false, (imm, rd))) =
      [BitVec.ofNat 8 ((arm8AddressWord imm rd >>> 0).toNat),
       BitVec.ofNat 8 ((arm8AddressWord imm rd >>> 8).toNat),
       BitVec.ofNat 8 ((arm8AddressWord imm rd >>> 16).toNat),
       BitVec.ofNat 8 ((arm8AddressWord imm rd >>> 24).toNat)] := by
  rw [arm8Encode, arm8Encode_address imm rd h]

/-- `arm8_ast` lowers an in-range `Loc` to the single `Address` instruction. -/
theorem arm8Ast_loc_small (register : Nat) (offset : BitVec 64)
    (h : arm8LocInRange offset = true) :
    arm8Ast (.loc register offset) = [.Address (false, offset, register)] := by
  simp only [arm8Ast]
  rw [ite_eq_left h]

/-- The encoded bytes of the in-range `Loc` lowering. -/
theorem arm8Enc_loc_small (register : Nat) (offset : BitVec 64)
    (h : arm8LocInRange offset = true) :
    arm8Enc (.loc register offset) = arm8Encode (.Address (false, offset, register)) := by
  rw [arm8Enc, arm8Ast_loc_small register offset h]
  simp

/-- The in-range `Loc` lowering encodes to four bytes. -/
theorem arm8Enc_loc_small_length (register : Nat) (offset : BitVec 64)
    (h : arm8LocInRange offset = true) :
    (arm8Enc (.loc register offset)).length = 4 := by
  rw [arm8Enc_loc_small register offset h]
  exact arm8Encode_length _

/-- The in-range `Loc` constructor of `encoder_correct arm8TargetL3`: the
single `Address` instruction writes `PC + offset` to the register and advances
`PC` by four.  `hrange` is HOL's own branch test -- the proof does
`Cases_on 'sw2sw INT_MINw <= c /\ c <= sw2sw INT_MAXw'` at `print_tac "Loc"`
-- not an added hypothesis: `Complete.lean` splits on it exactly as HOL does,
so the assembled `arm8EncoderCorrectL3` assumes nothing. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_loc_small (register : Nat) (offset : BitVec 64)
    (hrange : arm8LocInRange offset = true)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.loc register offset) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.loc register offset) s1 s2 ms := by
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
  have hregok : asmRegOkExact register arm8ConfigL3 = true := by
    have hk := hs.2.2.2.2.2.2
    simp only [asmOkExact, arm8ConfigL3, Bool.and_eq_true] at hk
    exact hk.1
  obtain ⟨hr_lt, hr_av, hr_31⟩ := regOk_of_asmL3 hregok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := (arm8Ok_iff ms).mp hok
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hlo := (arm8LocInRange_iff offset).mp hrange
  have hround := arm8AddressRoundtrip offset hlo.1 hlo.2
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.loc register offset)) ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hdom n hn)).symm⟩
  let w : BitVec 32 := arm8AddressWord offset (BitVec.ofNat 5 register)
  have henc := arm8Enc_loc_small register offset hrange
  rw [show ((register : BitVec 5)) = BitVec.ofNat 5 register from rfl] at henc
  have hlen := arm8Enc_loc_small_length register offset hrange
  rw [arm8EncodeBytes_address offset (BitVec.ofNat 5 register) hround] at henc
  have hbyte (i : Nat) (hi : i < 4) :
      ms.MEM (ms.PC + BitVec.ofNat 64 i) =
        (arm8Enc (.loc register offset)).getD i 0 :=
    bytesInMemoryHOL_get hbms i (by rw [hlen]; exact hi)
  have hb0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w >>> 0).toNat) := by
    have hh := hbyte 0 (by norm_num)
    rw [henc] at hh
    simpa [w] using hh
  have hb1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w >>> 8).toNat) := by
    have hh := hbyte 1 (by norm_num)
    rw [henc] at hh
    simpa [w] using hh
  have hb2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w >>> 16).toNat) := by
    have hh := hbyte 2 (by norm_num)
    rw [henc] at hh
    simpa [w] using hh
  have hb3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w >>> 24).toNat) := by
    have hh := hbyte 3 (by norm_num)
    rw [henc] at hh
    simpa [w] using hh
  let T1 : arm8_state :=
    { ms with
      branch_hint := none,
      REG := holUpdate (BitVec.ofNat 5 register) (ms.PC + offset) ms.REG,
      PC := ms.PC + 4 }
  have hT1pc : T1.PC = ms.PC + 4 := by rfl
  have hT1mem : ∀ x, T1.MEM x = ms.MEM x := by intro x; rfl
  have hn1 : arm8Next ms = T1 :=
    arm8Next_address ms offset register hr_31 hr_lt hround hexc0 hb0 hb1 hb2 hb3 hal he0 hel
  have hok1 : arm8Ok T1 = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, ?_⟩
    rw [hT1pc]
    rw [(alignedAddSub 2 ms.PC 4 (by rw [holAligned_iff]; decide)).1]
    exact halign
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  rw [hlen] at hupd
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 4 := by
    rw [← hupd]; simp [asmUpd, updPc]
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    intro x; rw [← hupd]; simp [asmUpd, updReg, updPc]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]; simp [asmUpd, updReg, updPc]
  have hs2regs : ∀ k, s2.regs k = if k = register then s1.pc + offset else s1.regs k := by
    intro k
    rw [← hupd]
    simp [asmUpd, updReg, updPc]
  have hq : targetStateRel arm8TargetL3 s2 T1 := by
    refine ⟨hok1, ?_, ?_, ?_, ?_⟩
    · change T1.PC = s2.pc
      rw [hT1pc, hs2pc, hpc]
      simp
    · change ∀ a, s2.memDomain a → T1.MEM a = s2.mem a
      intro a ha
      rw [hT1mem, hs2mem]
      exact hmem a (hs2dom ▸ ha)
    · change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
        T1.REG (BitVec.ofNat 5 k) = s2.regs k
      intro k hk
      have hk32 : k < 32 := by simpa [arm8ConfigL3] using hk.1
      rw [hs2regs k]
      unfold T1
      simp only [Flapjack.RiscV.L3.holUpdate]
      by_cases h1 : k = register
      · rw [ite_eq_left (by rw [h1]), ite_eq_left h1, hpc]
      · have hne : (BitVec.ofNat 5 register) ≠ (BitVec.ofNat 5 k) := by
          intro hh
          exact h1 ((arm8Reg_eq hr_lt hk32).1 hh).symm
        rw [ite_eq_right hne, ite_eq_right h1]
        exact hreg k hk
    · intro k hk
      simp [arm8ConfigL3] at hk
  have hcode : allPcs 4 s1.pc 0 ⊆ s1.memDomain := by
    have h0' := bytesInMemory_allPcs
      (arm8Enc (.loc register offset)) s1.pc s1.mem s1.memDomain 0 hb
    rw [hlen] at h0'
    exact h0'
  refine ⟨0, ?_⟩
  intro env henv
  constructor
  · change targetStateRel arm8TargetL3 s2 (env 0 (arm8Next ms))
    rw [hn1]
    have hagree : Arm8L3Agree s2.memDomain (env 0 T1) T1 := by
      rw [← arm8Proj_eq_iff]
      have hh := henv 0 T1
      rw [hs2dom]
      exact hh
    exact targetStateRel_congr hagree hq
  · refine ⟨fun x _ => ?_, trivial⟩
    rw [hn1]

end Flapjack.Compiler.Encoders.Arm8.L3
