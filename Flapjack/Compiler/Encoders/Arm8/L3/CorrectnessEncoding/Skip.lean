module

public import Flapjack.Compiler.Encoders.Arm8.L3.Configuration
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Infrastructure

@[expose] public section

set_option maxHeartbeats 4000000

/-!
# L3 ARMv8 encoder correctness: the `Skip` case

The `Skip` constructor case of the L3 `encoder_correct arm8TargetL3` port,
mirroring `Flapjack/RiscV/CorrectnessEncoding/Skip.lean`:

* `arm8Ast_skip` / `arm8Enc_skip`: `Skip` lowers to `NoOperation` and encodes
  to the AArch64 `NOP` word `0xD503201F` (little-endian bytes `1F 20 03 D5`).
* `arm8Decode_nop`: the full rendered `Decode` returns
  `Hint SystemHintOp_NOP` on that word.
* `arm8Run_nop`: the full rendered `Run` leaves the state unchanged for
  `Hint SystemHintOp_NOP`.
* `arm8Mem_nop` / `arm8Fetch_nop`: the rendered `Mem`/`Fetch` read the four
  emitted bytes (through `holFor`, `CheckAlignment` and `BigEndian`) and
  return the `NOP` word without changing the state.
* `arm8Next_nop`: `NextStateARM8` advances the PC by four and clears
  `branch_hint`, returning `some`.
* `arm8_encoder_correct_skip`: the full `encoder_correct` `Skip` clause — the
  existential witness `n = 0`, every interference environment, the original
  code-byte/PC assertion, and the outside-domain byte conclusion.

The other `arm8_ast` cases of `encoder_correct` are not ported here.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- `Skip` lowers to the `NoOperation` instruction. -/
theorem arm8Ast_skip : arm8Ast (HolAsm.inst HolInst.skip) = [NoOperation] := rfl

/-- `NoOperation` encodes to the AArch64 `NOP` bytes. -/
theorem arm8Encode_nop : arm8Encode NoOperation =
    [BitVec.ofNat 8 31, BitVec.ofNat 8 32, BitVec.ofNat 8 3, BitVec.ofNat 8 213] := by
  simp [arm8Encode, Encode, NoOperation, SystemHintOp2num]

/-- `Skip` encodes to the AArch64 `NOP` bytes. -/
theorem arm8Enc_skip : arm8Enc (HolAsm.inst HolInst.skip) =
    [BitVec.ofNat 8 31, BitVec.ofNat 8 32, BitVec.ofNat 8 3, BitVec.ofNat 8 213] := by
  simp [arm8Enc, arm8Ast_skip, arm8Encode_nop]

/-- The emitted `Skip` encoding is four bytes long. -/
theorem arm8Enc_skip_length : (arm8Enc (HolAsm.inst HolInst.skip)).length = 4 := by
  rw [arm8Enc_skip]
  simp

/-- The rendered L3 `Decode` returns `Hint NOP` on the emitted `NOP` word. -/
theorem arm8Decode_nop :
    Decode (BitVec.ofNat 32 0xD503201F) =
      instruction.Hint SystemHintOp.SystemHintOp_NOP := by
  simp [Decode, boolify32]
  intro _ _
  have h3 : holV2w 3 [false, false, false] = (0 : BitVec 3) := by decide
  rw [h3]
  simp [num2SystemHintOp]

/-- The rendered L3 `Run` leaves the state unchanged for `Hint NOP`. -/
theorem arm8Run_nop (s : arm8_state) :
    Run (instruction.Hint SystemHintOp.SystemHintOp_NOP) s = s := by
  simp [Run, «dfn'Hint»]

/-- A valid alignment makes `CheckAlignment` leave the state unchanged
(Flapjack infrastructure; no separate HOL theorem). -/
theorem CheckAlignment_aligned (ms : arm8_state) (a : BitVec 64) (sz : Nat)
    (t : AccType) (w : Bool) (h : Aligned (TN := 64) (a, sz) = true) :
    CheckAlignment (a, (sz, (t, w))) ms = ms := by
  simp [CheckAlignment, h]

/-- Little-endian mode is off at EL0 with `SCTLR_EL1.E0E` clear (Flapjack
infrastructure; the HOL `BigEndian` clause). -/
theorem BigEndian_false (ms : arm8_state) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (he0 : ms.SCTLR_EL1.E0E = false) : BigEndian ms = false := by
  simp [BigEndian, hel, he0]

/-- `Mem` reads the four emitted `NOP` bytes and returns `0xD503201F` without
changing the state. -/
theorem arm8Mem_nop (ms : arm8_state)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 31) (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 32)
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 3) (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 213)
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    Mem (TN := 32) (ms.PC, (4, AccType.AccType_IFETCH)) ms =
      (BitVec.ofNat 32 0xD503201F, ms) := by
  simp only [Mem]
  simp [holFor]
  constructor
  · rw [CheckAlignment_aligned ms ms.PC 4 AccType.AccType_IFETCH false hal]
    rw [BigEndian_false ms hel he0]
    simp only [Bool.false_eq_true, ite_false, BitVec.ofNat_eq_ofNat] at *
    rw [h0, h1, h2, h3]
    decide
  · exact CheckAlignment_aligned ms ms.PC 4 AccType.AccType_IFETCH false hal

/-- `Fetch` reads the four emitted `NOP` bytes. -/
theorem arm8Fetch_nop (ms : arm8_state)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 31) (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 32)
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 3) (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 213)
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    Fetch ms = (BitVec.ofNat 32 0xD503201F, ms) := by
  simp only [Fetch]
  exact arm8Mem_nop ms h0 h1 h2 h3 hal he0 hel

/-- One `NextStateARM8` step on a state holding the emitted `NOP` bytes advances
the PC by four and clears `branch_hint`. -/
theorem arm8Next_nop (ms : arm8_state)
    (h0 : ms.MEM ms.PC = BitVec.ofNat 8 31) (h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 32)
    (h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 3) (h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 213)
    (hal : Aligned (TN := 64) (ms.PC, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (hexc : ms.exception = exception.NoException) :
    NextStateARM8 ms = some { ms with branch_hint := none, PC := ms.PC + 4 } := by
  have hfetch := arm8Fetch_nop { ms with branch_hint := none } h0 h1 h2 h3 hal he0 hel
  simp only [Next, NextStateARM8]
  rw [hfetch]
  simp [arm8Decode_nop, arm8Run_nop, hexc]

/-- The `Skip` constructor of `encoder_correct arm8TargetL3`: one
`NextStateARM8` step from a state holding the emitted `NOP` bytes only advances
the PC by four. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_skip (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (HolAsm.inst HolInst.skip) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    ∃ n : Nat, ∀ env : Nat → arm8_state → arm8_state,
      interferenceOk env (arm8Proj s1.memDomain) →
      let pcs := allPcs (arm8ConfigL3.encode (HolAsm.inst HolInst.skip)).length s1.pc
      asserts n (fun k s => env (n - k) (arm8Next s)) ms
        (fun ms' => arm8Ok ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → ms'.MEM pc = ms.MEM pc) ∧
          ms'.PC ∈ pcs arm8ConfigL3.codeAlignment)
        (fun ms' => targetStateRel arm8TargetL3 s2 ms') ∧
      asserts2 (n + 1) (fun k => env (n + 1 - k)) arm8Next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x → ms1.MEM x = ms2.MEM x) := by
  obtain ⟨hs, hr⟩ := h
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  rw [arm8Enc_skip] at hb
  obtain ⟨hok, hpc, hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change arm8Ok ms = true at hok
  change ms.PC = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.MEM a = s1.mem a at hmem
  change ∀ i, i < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains i = false →
    ms.REG (BitVec.ofNat 5 i) = s1.regs i at hreg
  have hdom := bytesInMemoryHOL_domain hb
  have hbm : bytesInMemoryHOL ms.PC (arm8Enc (HolAsm.inst HolInst.skip)) ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hdom n hn)).symm⟩
  have hlen : (arm8Enc (HolAsm.inst HolInst.skip)).length = 4 := arm8Enc_skip_length
  have h0 : ms.MEM ms.PC = BitVec.ofNat 8 31 := by
    have := bytesInMemoryHOL_get hbm 0 (by rw [hlen]; omega)
    rw [arm8Enc_skip] at this
    simpa using this
  have h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 32 := by
    have := bytesInMemoryHOL_get hbm 1 (by rw [hlen]; omega)
    rw [arm8Enc_skip] at this
    simpa using this
  have h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 3 := by
    have := bytesInMemoryHOL_get hbm 2 (by rw [hlen]; omega)
    rw [arm8Enc_skip] at this
    simpa using this
  have h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 213 := by
    have := bytesInMemoryHOL_get hbm 3 (by rw [hlen]; omega)
    rw [arm8Enc_skip] at this
    simpa using this
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hn := arm8Next_nop ms h0 h1 h2 h3 hal he0 hel hexc
  have hnext : arm8Next ms = { ms with branch_hint := none, PC := ms.PC + 4 } := by
    unfold arm8Next
    rw [hn]
    rfl
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  simp only [arm8Enc_skip, List.length_cons, List.length_nil] at hupd
  have hs2 : s2 = { s1 with pc := s1.pc + BitVec.ofNat 64 4 } := by
    rw [← hupd]
    simp [asmUpd, instUpd, updPc]
  have hs2dom : s2.memDomain = s1.memDomain := by rw [hs2]
  have hq : targetStateRel arm8TargetL3 s2 { ms with branch_hint := none, PC := ms.PC + 4 } := by
    rw [hs2]
    have h4 : holAligned 2 (4 : BitVec 64) = true := by
      rw [holAligned_iff]; decide
    have hal4 : holAligned 2 (ms.PC + 4) = true := by
      rw [(alignedAddSub 2 ms.PC 4 h4).1, halign]
    have hokPost : arm8Ok { ms with branch_hint := none, PC := ms.PC + 4 } = true := by
      simp [arm8Ok, hel, he0, hsa0, htbi1, htbi0, hexc]
      exact hal4
    refine ⟨hokPost, ?_, ?_, ?_, ?_⟩
    · simp [hpc]
    · intro a ha
      simp only [arm8TargetL3_getByte]
      exact hmem a ha
    · intro i hi
      simp only [arm8TargetL3_getReg]
      exact hreg i hi
    · intro i hi
      simp [arm8ConfigL3] at hi
  refine ⟨0, ?_⟩
  intro env hinter
  constructor
  · simp only [asserts]
    rw [hnext]
    have hproj := hinter 0 { ms with branch_hint := none, PC := ms.PC + 4 }
    have hproj' : arm8Proj s2.memDomain (env 0 { ms with branch_hint := none, PC := ms.PC + 4 }) =
        arm8Proj s2.memDomain { ms with branch_hint := none, PC := ms.PC + 4 } := by
      rw [hs2dom]
      exact hproj
    exact (arm8TargetL3_targetOk.2 _ _ s2 hproj').1.mpr hq
  · simp only [asserts2]
    rw [hnext]
    exact ⟨fun _ _ => rfl, trivial⟩

end Flapjack.Compiler.Encoders.Arm8.L3
