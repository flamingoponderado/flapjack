/- Native ADD/SLTU/OR execution infrastructure for the full AddCarry case.
These are compositions of the reviewed native decoder and step definitions,
not separately named HOL declarations. They retain all intrinsic operand aliases,
full current-core GPR projection (including scratch31), original domain memory,
and arbitrary original interference. Full encoder acceptance remains separate.
-/
import Flapjack.RiscV.CorrectnessEncoding.ConstExecution
import Flapjack.RiscV.CorrectnessEncoding.DecodeBinop
import Flapjack.RiscV.CorrectnessEncoding.DecodeSltu
import Flapjack.RiscV.L3.Step.RegisterComparison
import Flapjack.RiscV.L3.Step.RegisterALUStep
namespace Flapjack.RiscV.TargetProof.AddCarry
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.RiscV.Target
  Compiler.Encoders.AsmProps
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
/-- AddCarry-local composition infrastructure with no separately named HOL original. -/
inductive Op where
  | add | sltu | or
  deriving DecidableEq
/-- AddCarry-local composition infrastructure with no separately named HOL original. -/
def instructionOf (op : Op) (rd rs rt : BitVec 5) : instruction :=
  match op with
  | .add => .ArithR (.ADD (rd,rs,rt))
  | .sltu => .ArithR (.SLTU (rd,rs,rt))
  | .or => .ArithR (.OR (rd,rs,rt))
/-- AddCarry-local composition infrastructure with no separately named HOL original. -/
def valueOf (op : Op) (a b : BitVec 64) : BitVec 64 :=
  match op with
  | .add => a + b
  | .sltu => holV2w 64 [BitVec.ult a b]
  | .or => a ||| b
/-- AddCarry-local composition infrastructure with no separately named HOL original. -/
theorem run_eq (op : Op) (rd rs rt : BitVec 5) (ms : riscv_state)
    (ok : riscvOk ms = true) :
    Run (instructionOf op rd rs rt) ms =
      «write'GPR» (valueOf op (GPR rs ms) (GPR rt ms),rd) ms := by
  have arch := ((riscvOk_iff ms).mp ok).2.1
  cases op <;> simp [instructionOf, valueOf, Run, «dfn'ADD», «dfn'SLTU»,
    «dfn'OR», in32BitMode, curArch, architecture, MCSR, arch, GPR, gpr]
/-- AddCarry-local composition infrastructure with no separately named HOL original. -/
theorem next_eq (op : Op) (rd rs rt : BitVec 5) (ms : riscv_state)
    (rn : rd ≠ 0#5) (ok : riscvOk ms = true)
    (bytes : encodedInstructionBytes ms (instructionOf op rd rs rt)) :
    NextRISCV ms = some (writePost ms rd (valueOf op (GPR rs ms) (GPR rt ms))) := by
  have lowbits : (Encode (instructionOf op rd rs rt)).getLsbD 0 = true ∧
      (Encode (instructionOf op rd rs rt)).getLsbD 1 = true := by
    cases op
    all_goals
      simp only [instructionOf, Encode, Rtype, opc, BitVec.setWidth_eq, BitVec.getLsbD_append]
      simp
  have decode : DecodeAny (.Word (Encode (instructionOf op rd rs rt))) =
      instructionOf op rd rs rt := by
    cases op
    · exact decode_encode_add rd rs rt
    · exact decode_encode_sltu rd rs rt
    · exact decode_encode_or rd rs rt
  have fetchedOk : riscvOk {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} = true := ok
  have run := run_eq op rd rs rt {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} fetchedOk
  exact write_next ms _ _ rd _ rn ok decode run lowbits.1 lowbits.2
    bytes.1 bytes.2.1 bytes.2.2.1 bytes.2.2.2
/-- AddCarry-local composition infrastructure with no separately named HOL original. -/
theorem writePost_ok (ms : riscv_state) (rd : BitVec 5) (v : BitVec 64)
    (ok : riscvOk ms = true) : riscvOk (writePost ms rd v) = true := by
  have fields := (riscvOk_iff ms).mp ok
  apply (riscvOk_iff _).mpr
  simpa [writePost, holUpdate] using
    ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1,
      aligned_add_four _ fields.2.2.2.2⟩
/-- AddCarry-local composition infrastructure with no separately named HOL original. -/
theorem writePost_projection (d : BitVec 64 → Prop) (ms ns : riscv_state)
    (rd : BitVec 5) (v : BitVec 64) (h : riscvProj d ms = riscvProj d ns) :
    riscvProj d (writePost ms rd v) = riscvProj d (writePost ns rd v) := by
  simp only [riscvProj, Prod.mk.injEq] at h
  simpa [riscvProj, writePost, holUpdate] using
    ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,
      congrArg (holUpdate rd v) h.2.2.2.2.1,h.2.2.2.2.2.1,
      h.2.2.2.2.2.2⟩
/-- AddCarry-local composition infrastructure with no separately named HOL original. -/
theorem step_projection (d : BitVec 64 → Prop) (op : Op) (rd rs rt : BitVec 5)
    (ms ns : riscv_state) (h : riscvProj d ms = riscvProj d ns) :
    riscvProj d (writePost ms rd (valueOf op (GPR rs ms) (GPR rt ms))) =
      riscvProj d (writePost ns rd (valueOf op (GPR rs ns) (GPR rt ns))) := by
  have bank : ms.c_gpr ms.procID = ns.c_gpr ns.procID := by
    simp only [riscvProj, Prod.mk.injEq] at h
    exact h.2.2.2.2.1
  have rsEq : GPR rs ms = GPR rs ns := by simp [GPR,gpr,bank]
  have rtEq : GPR rt ms = GPR rt ns := by simp [GPR,gpr,bank]
  rw [rsEq,rtEq]
  exact writePost_projection d ms ns rd _ h
/-- AddCarry-local composition infrastructure with no separately named HOL original. -/
inductive Family : instruction → Prop
  | add (rd rs rt : BitVec 5) : Family (.ArithR (.ADD (rd,rs,rt)))
  | sltu (rd rs rt : BitVec 5) : Family (.ArithR (.SLTU (rd,rs,rt)))
  | or (rd rs rt : BitVec 5) : Family (.ArithR (.OR (rd,rs,rt)))
/-- AddCarry-local composition infrastructure with no separately named HOL original. -/
def destination (i : instruction) : BitVec 5 :=
  match i with
  | .ArithR (.ADD (rd,_,_)) | .ArithR (.SLTU (rd,_,_))
  | .ArithR (.OR (rd,_,_)) => rd
  | _ => 0#5
/-- AddCarry-local composition infrastructure with no separately named HOL original. -/
theorem native_step (i : instruction) (kind : Family i) (ms : riscv_state)
    (rn : destination i ≠ 0#5) (ok : riscvOk ms = true)
    (bytes : encodedInstructionBytes ms i) :
    NextRISCV ms = some (constStep i ms) := by
  cases kind
  all_goals rename_i rd rs rt
  all_goals simp only [destination] at rn
  · have next := next_eq .add rd rs rt ms rn ok bytes
    have run := run_eq .add rd rs rt ms ok
    simp only [instructionOf] at run
    simpa [constStep, run, instructionOf, valueOf, «write'GPR», «write'gpr»,
      writePost, rn] using next
  · have next := next_eq .sltu rd rs rt ms rn ok bytes
    have run := run_eq .sltu rd rs rt ms ok
    simp only [instructionOf] at run
    simpa [constStep, run, instructionOf, valueOf, «write'GPR», «write'gpr»,
      writePost, rn] using next
  · have next := next_eq .or rd rs rt ms rn ok bytes
    have run := run_eq .or rd rs rt ms ok
    simp only [instructionOf] at run
    simpa [constStep, run, instructionOf, valueOf, «write'GPR», «write'gpr»,
      writePost, rn] using next
/-- AddCarry-local composition infrastructure with no separately named HOL original. -/
theorem run_frame (i : instruction) (kind : Family i)
    (ms : riscv_state) (ok : riscvOk ms = true) :
    (Run i ms).procID = ms.procID ∧ (Run i ms).c_PC = ms.c_PC ∧
    (Run i ms).MEM8 = ms.MEM8 ∧ (Run i ms).c_MCSR = ms.c_MCSR ∧
    (Run i ms).c_NextFetch = ms.c_NextFetch ∧ (Run i ms).exception = ms.exception := by
  cases kind
  all_goals rename_i rd rs rt
  · rw [show Run (.ArithR (.ADD (rd,rs,rt))) ms = _ from run_eq .add rd rs rt ms ok]
    by_cases zero : rd = 0#5 <;> simp [«write'GPR», «write'gpr», zero]
  · rw [show Run (.ArithR (.SLTU (rd,rs,rt))) ms = _ from run_eq .sltu rd rs rt ms ok]
    by_cases zero : rd = 0#5 <;> simp [«write'GPR», «write'gpr», zero]
  · rw [show Run (.ArithR (.OR (rd,rs,rt))) ms = _ from run_eq .or rd rs rt ms ok]
    by_cases zero : rd = 0#5 <;> simp [«write'GPR», «write'gpr», zero]
/-- AddCarry-local composition infrastructure with no separately named HOL original. -/
theorem run_projection (d : BitVec 64 → Prop) (i : instruction)
    (kind : Family i) (ms ns : riscv_state) (ok : riscvOk ms = true)
    (h : riscvProj d ms = riscvProj d ns) :
    riscvProj d (Run i ms) = riscvProj d (Run i ns) := by
  have okNs : riscvOk ns = true := (riscv_ok_of_projection_eq d ms ns h).symm.trans ok
  have writeEq (rd : BitVec 5) (v : BitVec 64) :
      riscvProj d («write'GPR» (v,rd) ms) = riscvProj d («write'GPR» (v,rd) ns) := by
    by_cases zero : rd = 0#5
    · simpa [«write'GPR», zero] using h
    · have fields := h
      simp only [riscvProj, Prod.mk.injEq] at fields
      simpa [riscvProj, «write'GPR», «write'gpr», holUpdate, zero] using
        ⟨fields.1,fields.2.1,fields.2.2.1,fields.2.2.2.1,
          congrArg (holUpdate rd v) fields.2.2.2.2.1,
          fields.2.2.2.2.2.1,fields.2.2.2.2.2.2⟩
  have reads (r : BitVec 5) : GPR r ms = GPR r ns := by
    have fields := h
    simp only [riscvProj, Prod.mk.injEq] at fields
    simp [GPR,gpr,fields.2.2.2.2.1]
  cases kind
  all_goals rename_i rd rs rt
  · rw [show Run (.ArithR (.ADD (rd,rs,rt))) ms = _ from run_eq .add rd rs rt ms ok,
      show Run (.ArithR (.ADD (rd,rs,rt))) ns = _ from run_eq .add rd rs rt ns okNs,
      reads rs, reads rt]
    exact writeEq rd _
  · rw [show Run (.ArithR (.SLTU (rd,rs,rt))) ms = _ from run_eq .sltu rd rs rt ms ok,
      show Run (.ArithR (.SLTU (rd,rs,rt))) ns = _ from run_eq .sltu rd rs rt ns okNs,
      reads rs, reads rt]
    exact writeEq rd _
  · rw [show Run (.ArithR (.OR (rd,rs,rt))) ms = _ from run_eq .or rd rs rt ms ok,
      show Run (.ArithR (.OR (rd,rs,rt))) ns = _ from run_eq .or rd rs rt ns okNs,
      reads rs, reads rt]
    exact writeEq rd _
theorem step_frame (i : instruction) (kind : Family i)
    (ms : riscv_state) (ok : riscvOk ms = true) :
    (constStep i ms).procID = ms.procID ∧
    (constStep i ms).MEM8 = ms.MEM8 ∧
    (constStep i ms).c_PC ms.procID = ms.c_PC ms.procID + 4 := by
  have frame := run_frame i kind ms ok
  simp [constStep, frame.1, frame.2.1, frame.2.2.1, holUpdate]

/-- Original riscv_ok is preserved by the complete native step, including
alignment of PC+4; its RV64 condition discharges the SLTU mode guard. -/
theorem step_ok (i : instruction) (kind : Family i)
    (ms : riscv_state) (ok : riscvOk ms = true) :
    riscvOk (constStep i ms) = true := by
  have frame := run_frame i kind ms ok
  have fields := (riscvOk_iff ms).mp ok
  apply (riscvOk_iff _).mpr
  simpa [constStep, frame.1, frame.2.1, frame.2.2.2.1,
    frame.2.2.2.2.1, frame.2.2.2.2.2, holUpdate] using
    ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1,
      aligned_add_four _ fields.2.2.2.2⟩

/-- Complete native step congruence under the literal original projection.
Unlike Run-only congruence this includes PC+4; scratch31 remains observable.
No separately named HOL declaration is claimed. -/
theorem step_projection_eq (d : BitVec 64 → Prop) (i : instruction)
    (kind : Family i) (ms ns : riscv_state)
    (ok : riscvOk ms = true) (h : riscvProj d ms = riscvProj d ns) :
    riscvProj d (constStep i ms) = riscvProj d (constStep i ns) := by
  have okNs : riscvOk ns = true := (riscv_ok_of_projection_eq d ms ns h).symm.trans ok
  have fm := run_frame i kind ms ok
  have fn := run_frame i kind ns okNs
  have runH := run_projection d i kind ms ns ok h
  simp only [riscvProj, Prod.mk.injEq, fm.1, fn.1] at runH
  simp only [riscvProj, Prod.mk.injEq] at h
  simpa [riscvProj, constStep, fm.1, fn.1, fm.2.1, fn.2.1,
    fm.2.2.1, fn.2.2.1, fm.2.2.2.1, fn.2.2.2.1,
    fm.2.2.2.2.1, fn.2.2.2.2.1, fm.2.2.2.2.2, fn.2.2.2.2.2,
    holUpdate] using
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, runH.2.2.2.2.1,
      h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- Whole complete-step list congruence with native PC advancement. Untagged
infrastructure for full AddCarry execution; no target execution is assumed. -/
theorem step_list_projection (d : BitVec 64 → Prop) (is : List instruction)
    (kinds : ∀ i ∈ is, Family i) (ms ns : riscv_state)
    (ok : riscvOk ms = true) (h : riscvProj d ms = riscvProj d ns) :
    riscvProj d (is.foldl (fun s i => constStep i s) ms) =
      riscvProj d (is.foldl (fun s i => constStep i s) ns) := by
  induction is generalizing ms ns with
  | nil => exact h
  | cons i is ih =>
    simp only [List.foldl_cons]
    exact ih (fun j hj => kinds j (List.mem_cons_of_mem i hj))
      (constStep i ms) (constStep i ns) (step_ok i (kinds i (by simp)) ms ok)
      (step_projection_eq d i (kinds i (by simp)) ms ns ok h)

/-- Arbitrary complete native step lists retain their full original projection
under original interference, including PC advancement and scratch31. Untagged
composition infrastructure; no target run or scratch-preservation premise. -/
theorem interleaved_projection (d : BitVec 64 → Prop)
    (is : List instruction) (kinds : ∀ i ∈ is, Family i)
    (env : Nat → riscv_state → riscv_state) (index : Nat) (ms : riscv_state)
    (ok : riscvOk ms = true) (interference : interferenceOk env (riscvProj d)) :
    riscvProj d (constStepInterleaved env index is ms) =
      riscvProj d (is.foldl (fun s i => constStep i s) ms) := by
  induction is generalizing index ms with
  | nil => rfl
  | cons i is ih =>
    have kind := kinds i (by simp)
    have tailKinds : ∀ j ∈ is, Family j :=
      fun j hj => kinds j (List.mem_cons_of_mem i hj)
    have stepOk := step_ok i kind ms ok
    have hEnv := interference index (constStep i ms)
    have envOk : riscvOk (env index (constStep i ms)) = true :=
      (riscv_ok_of_projection_eq d _ _ hEnv).trans stepOk
    simp only [constStepInterleaved, List.foldl_cons]
    exact (ih tailKinds (index + 1) _ envOk).trans
      (step_list_projection d is tailKinds _ _ envOk hEnv)

/-- Complete pure-list native frame and total PC increment, for arbitrary
length and every intrinsic operand. The emitted-byte execution connection is
proved per instruction above; full encoded-list assertions remain open. -/
theorem step_list_frame (is : List instruction)
    (kinds : ∀ i ∈ is, Family i) (ms : riscv_state)
    (ok : riscvOk ms = true) :
    let final := is.foldl (fun s i => constStep i s) ms
    riscvOk final = true ∧ final.procID = ms.procID ∧ final.MEM8 = ms.MEM8 ∧
      final.c_PC final.procID = ms.c_PC ms.procID + BitVec.ofNat 64 (4 * is.length) := by
  induction is generalizing ms with
  | nil => simpa using ok
  | cons i is ih =>
    have kind := kinds i (by simp)
    have tailKinds : ∀ j ∈ is, Family j :=
      fun j hj => kinds j (List.mem_cons_of_mem i hj)
    have stepFrame := step_frame i kind ms ok
    have tail := ih tailKinds (constStep i ms) (step_ok i kind ms ok)
    simp only [List.foldl_cons]
    refine ⟨tail.1, tail.2.1.trans stepFrame.1, tail.2.2.1.trans stepFrame.2.1, ?_⟩
    rw [tail.2.2.2, stepFrame.1, stepFrame.2.2]
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add]
    change ms.c_PC ms.procID + 4 + BitVec.ofNat 64 (4 * is.length) =
      ms.c_PC ms.procID + (BitVec.ofNat 64 (4 * is.length) + 4)
    rw [BitVec.add_assoc, BitVec.add_comm (4 : BitVec 64) (BitVec.ofNat 64 (4 * is.length))]

/-- AddCarry-local composition infrastructure with no separately named HOL original. -/
theorem native_execute (d : BitVec 64 → Prop) (is : List instruction)
    (kinds : ∀ i ∈ is, Family i)
    (nonzero : ∀ i ∈ is, destination i ≠ 0#5)
    (env : Nat → riscv_state → riscv_state) (index : Nat) (ms : riscv_state)
    (ok : riscvOk ms = true)
    (bytes : bytesInMemoryHOL (ms.c_PC ms.procID) (is.flatMap riscvEncode) ms.MEM8 d)
    (interference : interferenceOk env (riscvProj d)) :
    constNativeExecute env index is ms = constStepInterleaved env index is ms := by
  induction is generalizing index ms with
  | nil => rfl
  | cons i is ih =>
    have kind := kinds i (by simp)
    have rn := nonzero i (by simp)
    have tailKinds : ∀ j ∈ is, Family j :=
      fun j hj => kinds j (List.mem_cons_of_mem i hj)
    have tailNonzero : ∀ j ∈ is, destination j ≠ 0#5 :=
      fun j hj => nonzero j (List.mem_cons_of_mem i hj)
    simp only [List.flatMap_cons, bytesInMemory_append] at bytes
    have native := native_step i kind ms rn ok (encoded_bytes_of_region d ms i bytes.1)
    have step : riscvTarget.next ms = constStep i ms := by
      change holThe (NextRISCV ms) = _
      rw [native]
      simp [holThe]
    have frame := step_frame i kind ms ok
    have stepOk := step_ok i kind ms ok
    have envProjection := interference index (constStep i ms)
    have envOk : riscvOk (env index (constStep i ms)) = true :=
      (riscv_ok_of_projection_eq d _ _ envProjection).trans stepOk
    have tailBytes : bytesInMemoryHOL
        ((constStep i ms).c_PC (constStep i ms).procID)
        (is.flatMap riscvEncode) (constStep i ms).MEM8 d := by
      simpa [frame.1, frame.2.1, frame.2.2, riscvEncode] using bytes.2
    have envBytes := bytes_projection_transfer d (constStep i ms)
      (env index (constStep i ms)) envProjection.symm _ _ tailBytes
    have pcEq : (env index (constStep i ms)).c_PC (env index (constStep i ms)).procID =
        (constStep i ms).c_PC (constStep i ms).procID := by
      have fields := envProjection
      simp only [riscvProj, Prod.mk.injEq] at fields
      exact fields.2.2.2.2.2.2
    rw [← pcEq] at envBytes
    simp only [constNativeExecute, constStepInterleaved, step]
    exact ih tailKinds tailNonzero (index + 1) _ envOk envBytes

/-- Full original projection of actual native execution, derived from emitted
bytes, equals the complete pure-step list effect, including scratch31 and PC.
No target execution hypothesis; not a separately named HOL theorem. -/
theorem execute_projection (d : BitVec 64 → Prop) (is : List instruction)
    (kinds : ∀ i ∈ is, Family i)
    (nonzero : ∀ i ∈ is, destination i ≠ 0#5)
    (env : Nat → riscv_state → riscv_state) (index : Nat) (ms : riscv_state)
    (ok : riscvOk ms = true)
    (bytes : bytesInMemoryHOL (ms.c_PC ms.procID) (is.flatMap riscvEncode) ms.MEM8 d)
    (interference : interferenceOk env (riscvProj d)) :
    riscvProj d (constNativeExecute env index is ms) =
      riscvProj d (is.foldl (fun s i => constStep i s) ms) := by
  rw [native_execute d is kinds nonzero env index ms ok bytes interference]
  exact interleaved_projection d is kinds env index ms ok interference

/-- Actual native list execution retains original validity, advances PC by
exactly four per instruction, and preserves every byte in the original domain.
The environment may change processor identity or memory outside that domain;
no stronger preservation premise is introduced. Untagged composition
infrastructure; original full encoder assertions remain separate open work. -/
theorem execute_frame (d : BitVec 64 → Prop) (is : List instruction)
    (kinds : ∀ i ∈ is, Family i)
    (nonzero : ∀ i ∈ is, destination i ≠ 0#5)
    (env : Nat → riscv_state → riscv_state) (index : Nat) (ms : riscv_state)
    (ok : riscvOk ms = true)
    (bytes : bytesInMemoryHOL (ms.c_PC ms.procID) (is.flatMap riscvEncode) ms.MEM8 d)
    (interference : interferenceOk env (riscvProj d)) :
    let final := constNativeExecute env index is ms
    riscvOk final = true ∧
      final.c_PC final.procID = ms.c_PC ms.procID + BitVec.ofNat 64 (4 * is.length) ∧
      ∀ a, d a → final.MEM8 a = ms.MEM8 a := by
  have pureFrame := step_list_frame is kinds ms ok
  have projection := execute_projection d is kinds nonzero env index ms ok bytes interference
  have finalOk := (riscv_ok_of_projection_eq d _ _ projection).trans pureFrame.1
  have pc := projection
  simp only [riscvProj, Prod.mk.injEq] at pc
  dsimp only
  refine ⟨finalOk, pc.2.2.2.2.2.2.trans pureFrame.2.2.2, ?_⟩
  intro a inside
  exact (projected_memory_eq d _ _ projection a inside).trans
    (congrFun pureFrame.2.2.1 a)

/-- The original asserts2 memory-frame conclusion for every native instruction
in the emitted list. Each native transition is derived from original bytes;
its full memory frame discharges the original outside-domain observation.
The original decreasing assertion counter corresponds to increasing environment
indices. Untagged composition infrastructure, not full encoder correctness. -/
theorem native_asserts2 (d : BitVec 64 → Prop) (is : List instruction)
    (kinds : ∀ i ∈ is, Family i)
    (nonzero : ∀ i ∈ is, destination i ≠ 0#5)
    (env : Nat → riscv_state → riscv_state) (index : Nat) (ms : riscv_state)
    (ok : riscvOk ms = true)
    (bytes : bytesInMemoryHOL (ms.c_PC ms.procID) (is.flatMap riscvEncode) ms.MEM8 d)
    (interference : interferenceOk env (riscvProj d)) :
    asserts2 is.length (fun k => env (index + is.length - k)) riscvTarget.next ms
      (fun before after => ∀ a, ¬ d a → before.MEM8 a = after.MEM8 a) := by
  induction is generalizing index ms with
  | nil => trivial
  | cons i is ih =>
    have kind := kinds i (by simp)
    have rn := nonzero i (by simp)
    have tailKinds : ∀ j ∈ is, Family j :=
      fun j hj => kinds j (List.mem_cons_of_mem i hj)
    have tailNonzero : ∀ j ∈ is, destination j ≠ 0#5 :=
      fun j hj => nonzero j (List.mem_cons_of_mem i hj)
    simp only [List.flatMap_cons, bytesInMemory_append] at bytes
    have native := native_step i kind ms rn ok (encoded_bytes_of_region d ms i bytes.1)
    have step : riscvTarget.next ms = constStep i ms := by
      change holThe (NextRISCV ms) = _
      rw [native]
      simp [holThe]
    have frame := step_frame i kind ms ok
    have stepOk := step_ok i kind ms ok
    have envProjection := interference index (constStep i ms)
    have envOk : riscvOk (env index (constStep i ms)) = true :=
      (riscv_ok_of_projection_eq d _ _ envProjection).trans stepOk
    have tailBytes : bytesInMemoryHOL
        ((constStep i ms).c_PC (constStep i ms).procID)
        (is.flatMap riscvEncode) (constStep i ms).MEM8 d := by
      simpa [frame.1, frame.2.1, frame.2.2, riscvEncode] using bytes.2
    have envBytes := bytes_projection_transfer d (constStep i ms)
      (env index (constStep i ms)) envProjection.symm _ _ tailBytes
    have pcEq : (env index (constStep i ms)).c_PC (env index (constStep i ms)).procID =
        (constStep i ms).c_PC (constStep i ms).procID := by
      have fields := envProjection
      simp only [riscvProj, Prod.mk.injEq] at fields
      exact fields.2.2.2.2.2.2
    rw [← pcEq] at envBytes
    have tail := ih tailKinds tailNonzero (index + 1) _ envOk envBytes
    simp only [List.length_cons, asserts2, step]
    have firstIndex : index + (is.length + 1) - (is.length + 1) = index := by omega
    rw [firstIndex]
    refine ⟨?_, ?_⟩
    · intro a _
      exact (congrFun frame.2.1 a).symm
    · have counters : index + (is.length + 1) = index + 1 + is.length := by omega
      simpa only [counters] using tail

end Flapjack.RiscV.TargetProof.AddCarry
