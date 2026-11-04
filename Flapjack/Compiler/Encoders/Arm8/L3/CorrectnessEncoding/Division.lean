import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Const
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Simulate

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

/-!
# The `div` constructor of `encoder_correct arm8TargetL3`

`arm8_ast` lowers `Arith (Div d n m)` to the single instruction
`Division@64 (1, false, m, n, d)`: a signed 64-bit divide of `n` by `m`, with
HOL's convention that a zero divisor yields zero.  The CakeML `asmSem` side
guards the divisor with `assert (q <> 0w)`, so a failing step has no successor
and the machine's zero-divisor branch is never reached on a successful step.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The word emitted for `Division@64`: HOL's `e_data` term
`0b10011011010 ++ Rm ++ 00001 ++ (!unsigned) ++ Rn ++ Rd` (Flapjack
infrastructure: a readable abbreviation for a mechanically rendered term). -/
def arm8DivisionWord (unsigned : Bool) (rm rn rd : BitVec 5) : BitVec 32 :=
  BitVec.setWidth 32 ((BitVec.ofNat 11 1238) ++
    BitVec.setWidth 21 (rm ++
      BitVec.setWidth 16 ((BitVec.ofNat 5 1) ++
        BitVec.setWidth 11 (holV2w 1 [!unsigned] ++
          BitVec.setWidth 10 (rn ++ rd)))))

/-- `e_data` of `Division@64` is the division word (Flapjack infrastructure; no
separately named HOL declaration). -/
theorem arm8EData_division (unsigned : Bool) (rm rn rd : BitVec 5) :
    e_data (.«Division@64» ((1 : BitVec 64), (unsigned, (rm, (rn, rd))))) =
      MachineCode.ARM8 (arm8DivisionWord unsigned rm rn rd) := by
  rfl

/-- `Encode` of `Division@64` is the division word (Flapjack infrastructure; no
separately named HOL declaration). -/
theorem arm8Encode_division (unsigned : Bool) (rm rn rd : BitVec 5) :
    Encode (.Data (.«Division@64» ((1 : BitVec 64), (unsigned, (rm, (rn, rd)))))) =
      MachineCode.ARM8 (arm8DivisionWord unsigned rm rn rd) := by
  simp only [Encode, arm8EData_division]

/-- The rendered `Decode` inverts `arm8DivisionWord` for the signed form used by
`arm8_ast`. -/
theorem arm8Decode_division (rm rn rd : BitVec 5) :
    Decode (arm8DivisionWord false rm rn rd) =
      instruction.Data (Data.«Division@64» ((1 : BitVec 64), (false, (rm, (rn, rd))))) := by
  simp only [arm8DivisionWord, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  simp [holV2w_one_true, holV2w_five]

/-- `Run` of `Division@64`: divide `Rn` by `Rm` and write the quotient to `Rd`,
with a zero divisor yielding zero (HOL's `dfn'Division` convention). -/
theorem arm8Run_division (unsigned : Bool) (rm rn rd : BitVec 5) (st : arm8_state) :
    Run (instruction.Data (Data.«Division@64» ((1 : BitVec 64), (unsigned, (rm, (rn, rd)))))) st =
      «write'X» ((if X (TN := 64) rm st == (0 : BitVec 64) then (0 : BitVec 64)
        else if unsigned then (X (TN := 64) rn st).udiv (X (TN := 64) rm st)
        else (X (TN := 64) rn st).sdiv (X (TN := 64) rm st)), rd) st := by
  simp only [Run, «dfn'Division»]
  rfl

/-! ## The `div` constructor -/

/-- The `div` constructor of `encoder_correct arm8TargetL3`, lowered to the
single instruction `Division@64`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_div (destination dividend divisor : Nat)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.arith (.div destination dividend divisor))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.arith (.div destination dividend divisor))) s1 s2 ms := by
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
  have hregok : (asmRegOkExact destination arm8ConfigL3 = true ∧
      asmRegOkExact dividend arm8ConfigL3 = true) ∧
      asmRegOkExact divisor arm8ConfigL3 = true := by
    have hk := hs.2.2.2.2.2.2
    simpa [asmOkExact, asmInstOkExact, asmArithOkExact, arm8ConfigL3,
      Bool.and_eq_true] using hk
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hregok.1.1
  obtain ⟨hnlt, hnav, hn31⟩ := regOk_of_asmL3 hregok.1.2
  obtain ⟨hdvlt, hdvav, hdv31⟩ := regOk_of_asmL3 hregok.2
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC
      (arm8Enc (.inst (.arith (.div destination dividend divisor)))) ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hdom n hn)).symm⟩
  have hast : arm8Ast (.inst (.arith (.div destination dividend divisor))) =
      [.Data (.«Division@64» (1, false, BitVec.ofNat 5 divisor, BitVec.ofNat 5 dividend,
        BitVec.ofNat 5 destination))] := by
    simp [arm8Ast]
  have henc : arm8Enc (.inst (.arith (.div destination dividend divisor))) =
      arm8Encode (.Data (.«Division@64» (1, false, BitVec.ofNat 5 divisor,
        BitVec.ofNat 5 dividend, BitVec.ofNat 5 destination))) := by
    rw [arm8Enc, hast]
    simp
  have hlen : (arm8Enc (.inst (.arith (.div destination dividend divisor)))).length = 4 := by
    rw [henc]; exact arm8Encode_length _
  let w : BitVec 32 := arm8DivisionWord false (BitVec.ofNat 5 divisor)
    (BitVec.ofNat 5 dividend) (BitVec.ofNat 5 destination)
  have h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w >>> 0).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 0 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, arm8Encode_division] at hh
    simp at hh
    simpa [w] using hh
  have h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w >>> 8).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 1 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, arm8Encode_division] at hh
    simp at hh
    simpa [w] using hh
  have h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w >>> 16).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 2 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, arm8Encode_division] at hh
    simp at hh
    simpa [w] using hh
  have h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w >>> 24).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 3 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, arm8Encode_division] at hh
    simp at hh
    simpa [w] using hh
  have hdec : Decode w = instruction.Data (Data.«Division@64»
      ((1 : BitVec 64), (false, (BitVec.ofNat 5 divisor, (BitVec.ofNat 5 dividend,
        BitVec.ofNat 5 destination))))) :=
    arm8Decode_division _ _ _
  let v : BitVec 64 := (s1.regs dividend).sdiv (s1.regs divisor)
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  rw [hlen] at hupd
  have hne : s1.regs divisor ≠ 0 := by
    have hf : s2.failed = false := by simpa using hs.2.2.2.2.2.1
    rw [← hupd] at hf
    simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc] at hf
    exact hf.1
  have hbr : (Run (instruction.Data (Data.«Division@64»
      ((1 : BitVec 64), (false, (BitVec.ofNat 5 divisor, (BitVec.ofNat 5 dividend,
        BitVec.ofNat 5 destination)))))) { ms with branch_hint := none }).branch_hint = none := by
    rw [arm8Run_division, arm8WriteX_of_valid _ _ hd31 hdlt]
  have hexc : (Run (instruction.Data (Data.«Division@64»
      ((1 : BitVec 64), (false, (BitVec.ofNat 5 divisor, (BitVec.ofNat 5 dividend,
        BitVec.ofNat 5 destination)))))) { ms with branch_hint := none }).exception =
      exception.NoException := by
    rw [arm8Run_division, arm8WriteX_of_valid _ _ hd31 hdlt]
    simpa using hexc0
  have hn := arm8Next_word ms w
    (instruction.Data (Data.«Division@64»
      ((1 : BitVec 64), (false, (BitVec.ofNat 5 divisor, (BitVec.ofNat 5 dividend,
        BitVec.ofNat 5 destination))))))
    hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  have hrun : Run (instruction.Data (Data.«Division@64»
      ((1 : BitVec 64), (false, (BitVec.ofNat 5 divisor, (BitVec.ofNat 5 dividend,
        BitVec.ofNat 5 destination)))))) { ms with branch_hint := none } =
      { ms with branch_hint := none, REG := holUpdate (BitVec.ofNat 5 destination) v ms.REG } := by
    rw [arm8Run_division, arm8WriteX_of_valid _ _ hd31 hdlt]
    have hXm : X (TN := 64) (BitVec.ofNat 5 divisor) { ms with branch_hint := none } =
        s1.regs divisor := by
      rw [arm8X_of_valid _ hdv31 hdvlt]
      exact hreg divisor ⟨hdvlt, hdvav⟩
    have hXn : X (TN := 64) (BitVec.ofNat 5 dividend) { ms with branch_hint := none } =
        s1.regs dividend := by
      rw [arm8X_of_valid _ hn31 hnlt]
      exact hreg dividend ⟨hnlt, hnav⟩
    simp only [hXm, hXn, holUpdate]
    rw [if_neg (by intro h0; exact hne (by simpa using h0))]
    simp [v]
  have hnext : arm8Next ms = { ms with branch_hint := none, REG := holUpdate (BitVec.ofNat 5 destination) v ms.REG, PC := ms.PC + 4 } := by
    unfold arm8Next
    rw [hn, hrun]
    rfl
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 4 := by
    rw [← hupd]; simp [asmUpd, instUpd, arithUpd, updPc]
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    intro x; rw [← hupd]; simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]; simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc]
  have hs2regs : ∀ k, s2.regs k = if k = destination then v else s1.regs k := by
    intro k
    rw [← hupd]
    simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc, v,
      Flapjack.Compiler.Encoders.AsmSem.readReg]
  refine asmCaseOne (.arith (.div destination dividend divisor)) destination v
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

end Flapjack.Compiler.Encoders.Arm8.L3
