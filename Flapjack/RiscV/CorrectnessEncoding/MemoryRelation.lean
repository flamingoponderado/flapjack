import Flapjack.RiscV.CorrectnessEncoding.MemoryInputs
import Flapjack.RiscV.CorrectnessEncoding.MemoryRead
import Flapjack.RiscV.CorrectnessEncoding.MemoryStore
import Flapjack.RiscV.CorrectnessEncoding.MemoryStep
import Flapjack.RiscV.CorrectnessEncoding.Length

/-! Complete post-state relation infrastructure for the original Mem case.
The local compositions have no separately named HOL originals and stay untagged.
Source comparison follows literal asmSem mem_load/mem_store/mem_op/asm_step,
the native eight Run clauses and the original target_state_rel. The full Mem
encoder still requires original all-environment assertions and assembly. -/
namespace Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.RiscV.Target Compiler.Backend.LabToTarget
set_option autoImplicit false
set_option maxRecDepth 20000

/-- Literal source load frame at arbitrary positive width, count, endian and
failure flag. Completed register writes survive failed assertions. -/
theorem source_memload_frame {width : Nat} [NeZero width]
    (n r : Nat) (a : HolAddr width) (s : AsmState width) :
    (memLoad n r a s).mem = s.mem ∧
    (memLoad n r a s).memDomain = s.memDomain ∧
    (memLoad n r a s).fpRegs = s.fpRegs ∧
    (memLoad n r a s).pc = s.pc ∧
    (memLoad n r a s).lr = s.lr ∧
    (memLoad n r a s).be = s.be ∧
    (memLoad n r a s).align = s.align ∧
    (memLoad n r a s).regs = fun i =>
      if i = r then (memLoad n r a s).regs r else s.regs i := by
  simp [asm_memLoad_eq, assertState, updReg]

private theorem source_register_encoding (r : Nat)
    (ok : asmRegOkExact r riscvConfig = true) :
    r < 32 ∧ BitVec.ofNat 5 r ≠ 0#5 := by
  have guards : r < riscvConfig.regCount ∧ riscvConfig.avoidRegs.contains r = false := by
    simpa [asmRegOkExact, Bool.and_eq_true] using ok
  have bound : r < 32 := guards.1
  refine ⟨bound, ?_⟩
  intro zero
  have eq := congrArg BitVec.toNat zero
  simp only [BitVec.toNat_ofNat] at eq
  norm_num at eq
  rw [Nat.mod_eq_of_lt bound] at eq
  subst r
  simpa [riscvConfig] using guards.2

private theorem source_register_encoding_injective (i r : Nat)
    (ibound : i < 32) (rbound : r < 32) :
    BitVec.ofNat 5 i = BitVec.ofNat 5 r ↔ i = r := by
  constructor
  · intro eq
    have n := congrArg BitVec.toNat eq
    simpa only [BitVec.toNat_ofNat, show 2 ^ 5 = 32 by decide,
      Nat.mod_eq_of_lt ibound, Nat.mod_eq_of_lt rbound] using n
  · rintro rfl
    rfl

/-- The original source step fixes the complete source post-state with its
actual singleton memory encoding length; the source operation precedes PC4. -/
theorem memory_source_post (m : HolMemop) (r base : Nat) (w : BitVec 64)
    (s s' : AsmState 64)
    (step : asmStep riscvConfig s (.inst (.mem m r (.addr base w))) s') :
    s' = updPc (s.pc + 4) (memOp m r (.addr base w) s) := by
  have update := step.2.2.2.2.1
  cases m <;>
    simpa [asmUpd, instUpd, riscvConfig, riscvEnc_length_eq,
      riscvAst, riscvMemop] using update.symm

private theorem memory_emitted_kind (m : HolMemop) (r base : Nat) (w : BitVec 64)
    (native : instruction)
    (emitted : native ∈ riscvAst (.inst (.mem m r (.addr base w)))) :
    MemoryInstruction native := by
  cases m
  all_goals
    simp only [riscvAst, riscvMemop, List.mem_singleton] at emitted
    subst native
    constructor

private theorem load_data_relation (r : Nat) (a : HolAddr 64)
    (s : AsmState 64) (t : riscv_state) (k : Fin 4)
    (little : s.be = false)
    (success : (memLoad ((2 : Nat) ^ k.val) r a s).failed = false)
    (ok : asmRegOkExact r riscvConfig = true)
    (relation : targetStateRel riscvTarget s t) :
    let value := ((rawReadData (addrHOL a s) t).extractLsb' 0
      ((2 : Nat) ^ k.val * 8)).setWidth 64
    let post := «write'GPR» (value, BitVec.ofNat 5 r) t
    (∀ x, (memLoad ((2 : Nat) ^ k.val) r a s).memDomain x →
      post.MEM8 x = (memLoad ((2 : Nat) ^ k.val) r a s).mem x) ∧
    (∀ i, i < riscvConfig.regCount ∧ riscvConfig.avoidRegs.contains i = false →
      post.c_gpr post.procID (BitVec.ofNat 5 i) =
        (memLoad ((2 : Nat) ^ k.val) r a s).regs i) := by
  dsimp only
  have guard := source_register_encoding r ok
  have frame := source_memload_frame ((2 : Nat) ^ k.val) r a s
  have value := source_memload_native_value r a s t k little success relation
  have nonzero : (BitVec.ofNat 5 r == 0#5) = false := by
    simp only [beq_eq_false_iff_ne]
    exact guard.2
  constructor
  · intro x domain
    rw [frame.2.1] at domain
    have memory := relation.2.2.1 x domain
    change t.MEM8 x = s.mem x at memory
    simpa [«write'GPR», nonzero, «write'gpr», frame.1] using memory
  · intro i visible
    have bound : i < 32 := visible.1
    have before := relation.2.2.2.1 i visible
    change t.c_gpr t.procID (BitVec.ofNat 5 i) = s.regs i at before
    have eq := source_register_encoding_injective i r bound guard.1
    have regs := congrFun frame.2.2.2.2.2.2.2 i
    rw [regs]
    simp [«write'GPR», nonzero, «write'gpr», holUpdate]
    by_cases same : i = r
    · subst i
      simpa using value.symm
    · have different : BitVec.ofNat 5 i ≠ BitVec.ofNat 5 r :=
        fun sameEncoding => same (eq.mp sameEncoding)
      simpa [same, Ne.symm different] using before

private theorem store_data_relation (r : Nat) (a : HolAddr 64)
    (s : AsmState 64) (t : riscv_state) (k : Fin 4)
    (little : s.be = false)
    (success : (memStore ((2 : Nat) ^ k.val) r a s).failed = false)
    (relation : targetStateRel riscvTarget s t) :
    let post := rawWriteData (addrHOL a s, readReg r s, (2 : Nat) ^ k.val) t
    (∀ x, (memStore ((2 : Nat) ^ k.val) r a s).memDomain x →
      post.MEM8 x = (memStore ((2 : Nat) ^ k.val) r a s).mem x) ∧
    (∀ i, i < riscvConfig.regCount ∧ riscvConfig.avoidRegs.contains i = false →
      post.c_gpr post.procID (BitVec.ofNat 5 i) =
        (memStore ((2 : Nat) ^ k.val) r a s).regs i) := by
  dsimp only
  constructor
  · intro x domain
    exact (source_memstore_native_memory r a s t k little success relation x domain).symm
  · intro i visible
    rw [rawWriteDataPreservesNonMemory,
      (source_memstore_frame ((2 : Nat) ^ k.val) r a s).2.1]
    exact relation.2.2.2.1 i visible

private theorem raw_read_skip (p : BitVec 64) (t : riscv_state)
    (skip : BitVec 8 → BitVec 64) :
    rawReadData p {t with c_Skip := skip} = rawReadData p t := rfl

private theorem raw_write_skip (p value : BitVec 64) (n : Nat) (t : riscv_state)
    (skip : BitVec 8 → BitVec 64) :
    rawWriteData (p, value, n) {t with c_Skip := skip} =
      {rawWriteData (p, value, n) t with c_Skip := skip} := by
  unfold rawWriteData
  dsimp only
  split <;> (try split) <;> rfl

/-- Actual native memory step's observed memory and current-core registers are
exactly those of actual Run. Fetch's Skip4 and Next's PC update do not alter
these fields. All intrinsic registers, offsets and addresses are unrestricted. -/
theorem memory_step_data_frame (native : instruction) (kind : MemoryInstruction native)
    (t : riscv_state) (valid : riscvOk t = true) :
    (memoryStep native t).MEM8 = (Run native t).MEM8 ∧
    (memoryStep native t).c_gpr (memoryStep native t).procID =
      (Run native t).c_gpr (Run native t).procID := by
  let fetched := {t with c_Skip := holUpdate t.procID 4 t.c_Skip}
  have validFetched : riscvOk fetched = true := by simpa [riscvOk, fetched] using valid
  dsimp only [memoryStep]
  cases kind
  all_goals
    first
    | rw [memory_run_ld _ _ _ fetched validFetched, memory_run_ld _ _ _ t valid]
    | rw [memory_run_lwu _ _ _ fetched validFetched, memory_run_lwu _ _ _ t valid]
    | rw [memory_run_lhu _ _ _ fetched validFetched, memory_run_lhu _ _ _ t valid]
    | rw [memory_run_lbu _ _ _ fetched validFetched, memory_run_lbu _ _ _ t valid]
    | rw [memory_run_sd _ _ _ fetched validFetched, memory_run_sd _ _ _ t valid]
    | rw [memory_run_sw _ _ _ fetched validFetched, memory_run_sw _ _ _ t valid]
    | rw [memory_run_sh _ _ _ fetched validFetched, memory_run_sh _ _ _ t valid]
    | rw [memory_run_sb _ _ _ fetched validFetched, memory_run_sb _ _ _ t valid]
  all_goals
    dsimp only [fetched]
    simp only [raw_read_skip, raw_write_skip]
    simp [«write'GPR», «write'gpr», GPR, gpr]
  all_goals split_ifs <;> simp

private theorem native_low_extract (n : Nat) (w : BitVec 64)
    (size : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) :
    RiscV.L3.holWordExtract n (n - 1) 0 w = w.extractLsb' 0 n := by
  rcases size with rfl | rfl | rfl | rfl
  all_goals
    apply BitVec.eq_of_toNat_eq
    simp [RiscV.L3.holWordExtract, BitVec.extractLsb'_toNat]
  all_goals exact w.isLt

/-- Whole original target relation after the actual native memory step, for
every source memory constructor. The only correctness premises are the original
source step and initial relation. Emitted-AST membership selects the original
singleton instruction; it assumes no target execution or result. The full Mem
encoder still needs original environment/assertion assembly. -/
theorem memory_step_post_relation (m : HolMemop) (r base : Nat) (w : BitVec 64)
    (s s' : AsmState 64) (t : riscv_state) (native : instruction)
    (step : asmStep riscvConfig s (.inst (.mem m r (.addr base w))) s')
    (relation : targetStateRel riscvTarget s t)
    (emitted : native ∈ riscvAst (.inst (.mem m r (.addr base w)))) :
    targetStateRel riscvTarget s' (memoryStep native t) := by
  have ok := step.2.2.2.2.2.2
  have kind := memory_emitted_kind m r base w native emitted
  have nativeControl := memory_step_ok_pc native kind t relation.1
  have nativeData := memory_step_data_frame native kind t relation.1
  have little : s.be = false := step.2.2.1
  have sourcePost := memory_source_post m r base w s s' step
  have success : (memOp m r (.addr base w) s).failed = false := by
    have success := step.2.2.2.2.2.1
    rw [sourcePost] at success
    simpa [updPc] using success
  have data :
      (∀ x, (memOp m r (.addr base w) s).memDomain x →
        (Run native t).MEM8 x = (memOp m r (.addr base w) s).mem x) ∧
      (∀ i, i < riscvConfig.regCount ∧ riscvConfig.avoidRegs.contains i = false →
        (Run native t).c_gpr (Run native t).procID (BitVec.ofNat 5 i) =
          (memOp m r (.addr base w) s).regs i) := by
    have regOk := (memory_source_guards m r base w ok).1
    cases m
    all_goals
      simp only [memOp] at success ⊢
      rw [memory_emitted_run _ r base w s t native ok relation emitted]
    · simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceDiv, BitVec.extractLsb'_eq_self, BitVec.setWidth_eq] using load_data_relation r (.addr base w) s t ⟨3,by decide⟩ little success regOk relation
    · simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceDiv, native_low_extract 8 _ (by simp)] using load_data_relation r (.addr base w) s t ⟨0,by decide⟩ little success regOk relation
    · simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceDiv, native_low_extract 16 _ (by simp)] using load_data_relation r (.addr base w) s t ⟨1,by decide⟩ little success regOk relation
    · simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceDiv, native_low_extract 32 _ (by simp)] using load_data_relation r (.addr base w) s t ⟨2,by decide⟩ little success regOk relation
    · simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceDiv, BitVec.extractLsb'_eq_self, BitVec.setWidth_eq] using store_data_relation r (.addr base w) s t ⟨3,by decide⟩ little success relation
    · simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceDiv, BitVec.extractLsb'_eq_self, BitVec.setWidth_eq] using store_data_relation r (.addr base w) s t ⟨0,by decide⟩ little success relation
    · simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceDiv, BitVec.extractLsb'_eq_self, BitVec.setWidth_eq] using store_data_relation r (.addr base w) s t ⟨1,by decide⟩ little success relation
    · simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceDiv, BitVec.extractLsb'_eq_self, BitVec.setWidth_eq] using store_data_relation r (.addr base w) s t ⟨2,by decide⟩ little success relation
  rw [sourcePost]
  refine ⟨nativeControl.1, ?_, ?_, ?_, ?_⟩
  · change (memoryStep native t).c_PC (memoryStep native t).procID = s.pc + 4
    rw [nativeControl.2]
    exact congrArg (fun pc => pc + 4) relation.2.1
  · intro x domain
    change (memoryStep native t).MEM8 x = (memOp m r (.addr base w) s).mem x
    rw [nativeData.1]
    exact data.1 x domain
  · intro i visible
    change (memoryStep native t).c_gpr (memoryStep native t).procID (BitVec.ofNat 5 i) =
      (memOp m r (.addr base w) s).regs i
    rw [nativeData.2]
    exact data.2 i visible
  · intro i bound
    change i < 0 at bound
    omega

end Flapjack.RiscV.TargetProof
