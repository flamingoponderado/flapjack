import Flapjack.RiscV.CorrectnessEncoding.MemoryBytes
import Flapjack.RiscV.CorrectnessEncoding.ConstNext
import Flapjack.RiscV.CorrectnessEncoding.DecodeMemory

/-! Native memory Next infrastructure for the original Mem constructor.
These compositions have no separately named HOL originals and remain untagged.
The full constructor still derives emitted bytes and source guards from its
original source step and initial state relation.

Source comparison: riscv_stepScript.sml:41-67 performs Fetch, DecodeAny, Run,
rejects non-NoException, then advances PC by Skip on the empty NextFetch arm.
The eight actual Run equations preserve procID, PC, Skip, MachineCSR,
NextFetch and exception, so fetched Skip4 supplies PC+4 without changing any
memory address restrictions. Original riscv_targetProofScript.sml:661-669
uses next_tac for all four load/store sizes. This module proves the native
composition only; source-domain alignment, interference and the complete
original encoder existential/assertions remain required in the full Mem bead. -/
namespace Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.RiscV.Target
set_option autoImplicit false

/-- The eight literal memory families emitted by the original target.
Local case inventory, not a replacement instruction carrier. -/
inductive MemoryInstruction : instruction → Prop where
  | ld (r1 r2 : BitVec 5) (offs : BitVec 12) : MemoryInstruction (.Load (.LD (r1,r2,offs)))
  | lwu (r1 r2 : BitVec 5) (offs : BitVec 12) : MemoryInstruction (.Load (.LWU (r1,r2,offs)))
  | lhu (r1 r2 : BitVec 5) (offs : BitVec 12) : MemoryInstruction (.Load (.LHU (r1,r2,offs)))
  | lbu (r1 r2 : BitVec 5) (offs : BitVec 12) : MemoryInstruction (.Load (.LBU (r1,r2,offs)))
  | sd (r1 r2 : BitVec 5) (offs : BitVec 12) : MemoryInstruction (.Store (.SD (r1,r2,offs)))
  | sw (r1 r2 : BitVec 5) (offs : BitVec 12) : MemoryInstruction (.Store (.SW (r1,r2,offs)))
  | sh (r1 r2 : BitVec 5) (offs : BitVec 12) : MemoryInstruction (.Store (.SH (r1,r2,offs)))
  | sb (r1 r2 : BitVec 5) (offs : BitVec 12) : MemoryInstruction (.Store (.SB (r1,r2,offs)))

/-- Complete native memory Run preserves all non-memory/non-register control
fields under original fixed-target validity. Effects are proved, not assumed.
There is no separately named HOL theorem for this composition. -/
theorem memory_run_control_frame (i : instruction) (kind : MemoryInstruction i)
    (ms : riscv_state) (ok : riscvOk ms = true) :
    (Run i ms).procID = ms.procID ∧ (Run i ms).c_PC = ms.c_PC ∧
    (Run i ms).c_Skip = ms.c_Skip ∧ (Run i ms).c_MCSR = ms.c_MCSR ∧
    (Run i ms).c_NextFetch = ms.c_NextFetch ∧
    (Run i ms).exception = ms.exception := by
  cases kind
  · rw [memory_run_ld _ _ _ ms ok]
    simp only [«write'GPR», «write'gpr»]
    split <;> simp
  · rw [memory_run_lwu _ _ _ ms ok]
    simp only [«write'GPR», «write'gpr»]
    split <;> simp
  · rw [memory_run_lhu _ _ _ ms ok]
    simp only [«write'GPR», «write'gpr»]
    split <;> simp
  · rw [memory_run_lbu _ _ _ ms ok]
    simp only [«write'GPR», «write'gpr»]
    split <;> simp
  · rw [memory_run_sd _ _ _ ms ok]
    rw [rawWriteDataPreservesNonMemory]
    simp
  · rw [memory_run_sw _ _ _ ms ok]
    rw [rawWriteDataPreservesNonMemory]
    simp
  · rw [memory_run_sh _ _ _ ms ok]
    rw [rawWriteDataPreservesNonMemory]
    simp
  · rw [memory_run_sb _ _ _ ms ok]
    rw [rawWriteDataPreservesNonMemory]
    simp

private theorem byte0 (w : BitVec 32) :
    RiscV.L3.holWordExtract 8 7 0 w = BitVec.extractLsb' 0 8 w := by
  apply BitVec.eq_of_toNat_eq
  simp [RiscV.L3.holWordExtract, BitVec.extractLsb'_toNat]

private theorem byte1 (w : BitVec 32) :
    RiscV.L3.holWordExtract 8 15 8 w = BitVec.extractLsb' 8 8 w := by
  apply BitVec.eq_of_toNat_eq
  simp [RiscV.L3.holWordExtract, BitVec.extractLsb'_toNat]

private theorem byte2 (w : BitVec 32) :
    RiscV.L3.holWordExtract 8 23 16 w = BitVec.extractLsb' 16 8 w := by
  apply BitVec.eq_of_toNat_eq
  simp [RiscV.L3.holWordExtract, BitVec.extractLsb'_toNat]

private theorem byte3 (w : BitVec 32) :
    RiscV.L3.holWordExtract 8 31 24 w = BitVec.extractLsb' 24 8 w := by
  apply BitVec.eq_of_toNat_eq
  simp [RiscV.L3.holWordExtract, BitVec.extractLsb'_toNat]

private theorem reassemble (w : BitVec 32) :
    RiscV.L3.holWordExtract 8 31 24 w ++
      (RiscV.L3.holWordExtract 8 23 16 w ++
        (RiscV.L3.holWordExtract 8 15 8 w ++
          RiscV.L3.holWordExtract 8 7 0 w)) = w := by
  rw [byte0,byte1,byte2,byte3]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

private theorem encoded_fetch (ms : riscv_state) (w : BitVec 32)
    (vm : (ms.c_MCSR ms.procID).mstatus.VM = 0)
    (low0 : w.getLsbD 0 = true) (low1 : w.getLsbD 1 = true)
    (b0 : ms.MEM8 (ms.c_PC ms.procID) = RiscV.L3.holWordExtract 8 7 0 w)
    (b1 : ms.MEM8 (ms.c_PC ms.procID + 1) = RiscV.L3.holWordExtract 8 15 8 w)
    (b2 : ms.MEM8 (ms.c_PC ms.procID + 2) = RiscV.L3.holWordExtract 8 23 16 w)
    (b3 : ms.MEM8 (ms.c_PC ms.procID + 3) = RiscV.L3.holWordExtract 8 31 24 w) :
    Fetch ms = (.Word w, {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip}) := by
  change ms.MEM8 (ms.c_PC ms.procID + 1#64) = _ at b1
  change ms.MEM8 (ms.c_PC ms.procID + 2#64) = _ at b2
  change ms.MEM8 (ms.c_PC ms.procID + 3#64) = _ at b3
  rw [fetch_bare ms vm]
  have lo0 : (RiscV.L3.holWordExtract 8 7 0 w).getLsbD 0 = true := by
    simpa [byte0] using low0
  have lo1 : (RiscV.L3.holWordExtract 8 7 0 w).getLsbD 1 = true := by
    simpa [byte0] using low1
  simp [rawReadInst, boolify8, b0, b1, b2, b3, lo0, lo1, «write'Skip»]
  exact reassemble w

/-- Complete normal-control native memory step, including fetched Skip4 and
PC advancement. Untagged composition, not an assumed target result. -/
noncomputable def memoryStep (i : instruction) (ms : riscv_state) : riscv_state :=
  let fetched := {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip}
  let post := Run i fetched
  {post with c_PC := holUpdate post.procID (post.c_PC post.procID + 4) post.c_PC}

/-- Actual Next for every emitted memory family. Original validity and emitted
bytes suffice; no successful target Run, target result, nonzero-register or
memory-address hypothesis is assumed. The full encoder derives these byte
premises from its original source step and initial relation. -/
theorem next_memory_step (i : instruction) (kind : MemoryInstruction i)
    (ms : riscv_state) (ok : riscvOk ms = true)
    (bytes : encodedInstructionBytes ms i) :
    NextRISCV ms = some (memoryStep i ms) := by
  have decode : DecodeAny (.Word (Encode i)) = i := by
    cases kind
    · exact decode_encode_ld _ _ _
    · exact decode_encode_lwu _ _ _
    · exact decode_encode_lhu _ _ _
    · exact decode_encode_lbu _ _ _
    · exact decode_encode_sd _ _ _
    · exact decode_encode_sw _ _ _
    · exact decode_encode_sh _ _ _
    · exact decode_encode_sb _ _ _
  have lowbits : (Encode i).getLsbD 0 = true ∧ (Encode i).getLsbD 1 = true := by
    cases kind
    all_goals
      simp only [Encode, Itype, Stype, opc, BitVec.setWidth_eq, BitVec.getLsbD_append]
      simp
  let fetched : riscv_state := {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip}
  have fok : riscvOk fetched = true := by
    simpa [riscvOk, fetched] using ok
  have frame := memory_run_control_frame i kind fetched fok
  have fields := (riscvOk_iff ms).mp ok
  have fetch := encoded_fetch ms (Encode i) fields.1 lowbits.1 lowbits.2
    bytes.1 bytes.2.1 bytes.2.2.1 bytes.2.2.2
  have next := nextRISCV ms (.Word (Encode i)) fetched i (Run i fetched)
    ⟨fetch, decode, rfl, frame.2.2.2.2.2.trans fields.2.2.2.1,
      by rw [frame.1, frame.2.2.2.2.1]; exact fields.2.2.1⟩
  let post := Run i fetched
  change NextRISCV ms = some {post with c_PC := holUpdate post.procID (post.c_PC post.procID + 4) post.c_PC}
  simpa only [post, update_pc, «write'PC», Skip, frame.1, frame.2.2.1,
    show fetched.c_Skip fetched.procID = 4 from by simp [fetched, holUpdate]] using next

/-- Complete memory step preserves fixed-target validity and advances PC by
four, with no address, register or target-run assumptions. Untagged local
consequence of the actual Next composition. -/
theorem memory_step_ok_pc (i : instruction) (kind : MemoryInstruction i)
    (ms : riscv_state) (ok : riscvOk ms = true) :
    riscvOk (memoryStep i ms) = true ∧
      (memoryStep i ms).c_PC (memoryStep i ms).procID = ms.c_PC ms.procID + 4 := by
  let fetched : riscv_state := {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip}
  have fok : riscvOk fetched = true := by simpa [riscvOk, fetched] using ok
  have frame := memory_run_control_frame i kind fetched fok
  have fields := (riscvOk_iff ms).mp ok
  constructor
  · change riscvOk {Run i fetched with c_PC := holUpdate (Run i fetched).procID ((Run i fetched).c_PC (Run i fetched).procID + 4) (Run i fetched).c_PC} = true
    apply (riscvOk_iff _).mpr
    dsimp only
    rw [frame.1, frame.2.1, frame.2.2.2.1,
      frame.2.2.2.2.1, frame.2.2.2.2.2]
    simpa only [fetched, holUpdate, ite_true] using
      (show (ms.c_MCSR ms.procID).mstatus.VM = 0 ∧
        (ms.c_MCSR ms.procID).mcpuid.ArchBase = 2 ∧
        ms.c_NextFetch ms.procID = none ∧ ms.exception = exception.NoException ∧
        holAligned 2 (ms.c_PC ms.procID + 4) = true from
        ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1,
          aligned_add_four _ fields.2.2.2.2⟩)
  · change (holUpdate (Run i fetched).procID
      ((Run i fetched).c_PC (Run i fetched).procID + 4)
      (Run i fetched).c_PC) (Run i fetched).procID = _
    rw [frame.1, frame.2.1]
    simp [holUpdate, fetched]

end Flapjack.RiscV.TargetProof
