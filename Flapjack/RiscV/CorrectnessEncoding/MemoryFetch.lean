import Flapjack.RiscV.CorrectnessEncoding.MemoryStep
import Flapjack.RiscV.CorrectnessEncoding.BytesInMemory

/-! Actual native memory Fetch/Next from original source instruction bytes.
Local untagged compositions have no separately named HOL originals. The
source asmStep supplies bytes_in_memory; the initial complete target relation
transports them to the native state. Native decoding and execution are derived,
not assumed. Full Mem environment/assertion assembly remains separate. -/
namespace Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.AsmSem Compiler.Encoders.RiscV.Target
set_option autoImplicit false

/-- Actual singleton memory encoding, including every original register and
word64 offset. Membership selects its emitted native instruction only. -/
theorem memory_singleton_encoding (m : HolMemop) (r base : Nat) (w : BitVec 64)
    (native : instruction)
    (emitted : native ∈ riscvAst (.inst (.mem m r (.addr base w)))) :
    riscvConfig.encode (.inst (.mem m r (.addr base w))) = riscvEncode native := by
  cases m
  all_goals
    simp only [riscvAst, riscvMemop, List.mem_singleton] at emitted
    subst native
    simp [riscvConfig, riscvEnc, riscvAst, riscvMemop]

/-- All four actual native instruction bytes are obtained from the original
source step, with no extra native-byte assumption. -/
theorem memory_source_encoded_bytes (m : HolMemop) (r base : Nat) (w : BitVec 64)
    (s s' : AsmState 64) (t : riscv_state) (native : instruction)
    (step : asmStep riscvConfig s (.inst (.mem m r (.addr base w))) s')
    (relation : targetStateRel riscvTarget s t)
    (emitted : native ∈ riscvAst (.inst (.mem m r (.addr base w)))) :
    encodedInstructionBytes t native := by
  have bytes := step.1
  rw [memory_singleton_encoding m r base w native emitted] at bytes
  change bytesInMemoryHOL s.pc
    [RiscV.L3.holWordExtract 8 7 0 (Encode native),
     RiscV.L3.holWordExtract 8 15 8 (Encode native),
     RiscV.L3.holWordExtract 8 23 16 (Encode native),
     RiscV.L3.holWordExtract 8 31 24 (Encode native)] s.mem s.memDomain at bytes
  have transported := bytes_in_memory_thm () s t _ _ _ _ ⟨relation,bytes⟩
  exact ⟨transported.2.2.2.2.2.1, transported.2.2.2.2.2.2.1,
    transported.2.2.2.2.2.2.2.1, transported.2.2.2.2.2.2.2.2.1⟩

/-- Actual native Next for all eight original source memory constructors.
The only correctness premises are original asmStep and initial target relation;
no target execution/result, byte observation or extra guard is assumed. -/
theorem memory_source_next (m : HolMemop) (r base : Nat) (w : BitVec 64)
    (s s' : AsmState 64) (t : riscv_state) (native : instruction)
    (step : asmStep riscvConfig s (.inst (.mem m r (.addr base w))) s')
    (relation : targetStateRel riscvTarget s t)
    (emitted : native ∈ riscvAst (.inst (.mem m r (.addr base w)))) :
    NextRISCV t = some (memoryStep native t) := by
  have kind : MemoryInstruction native := by
    cases m
    all_goals
      simp only [riscvAst, riscvMemop, List.mem_singleton] at emitted
      subst native
      constructor
  exact next_memory_step native kind t relation.1
    (memory_source_encoded_bytes m r base w s s' t native step relation emitted)

end Flapjack.RiscV.TargetProof
