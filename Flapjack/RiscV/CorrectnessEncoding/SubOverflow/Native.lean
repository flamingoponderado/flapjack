import Flapjack.RiscV.CorrectnessEncoding.ConstExecution
import Flapjack.RiscV.CorrectnessEncoding.DecodeBinop
import Flapjack.RiscV.CorrectnessEncoding.DecodeConst
import Flapjack.RiscV.CorrectnessEncoding.DecodeShift
import Flapjack.RiscV.L3.Step.RegisterALUStep
import Flapjack.RiscV.CorrectnessEncoding.ShiftRun
namespace Flapjack.RiscV.TargetProof.SubOverflow
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.RiscV.Target
  Compiler.Encoders.AsmProps
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
/-- The five literal native families used by the six SubOverflow instructions.
Untagged local composition infrastructure; no separately named HOL declaration. -/
inductive Family : instruction → Prop
  | xor (rd rs rt : BitVec 5) : Family (.ArithR (.XOR (rd,rs,rt)))
  | xori (rd rs : BitVec 5) (imm : BitVec 12) : Family (.ArithI (.XORI (rd,rs,imm)))
  | sub (rd rs rt : BitVec 5) : Family (.ArithR (.SUB (rd,rs,rt)))
  | and (rd rs rt : BitVec 5) : Family (.ArithR (.AND (rd,rs,rt)))
  | srli (rd rs : BitVec 5) (imm : BitVec 6) : Family (.Shift (.SRLI (rd,rs,imm)))
/-- Family-local destination. The fallback is excluded by Family proofs. -/
def destination : instruction → BitVec 5
  | .ArithR (.XOR (rd,_,_)) | .ArithI (.XORI (rd,_,_))
  | .ArithR (.SUB (rd,_,_)) | .ArithR (.AND (rd,_,_))
  | .Shift (.SRLI (rd,_,_)) => rd
  | _ => 0
/-- Literal native Run values, restricted by Family in every effect theorem. -/
def value (i : instruction) (ms : riscv_state) : BitVec 64 :=
  match i with
  | .ArithR (.XOR (_,rs,rt)) => GPR rs ms ^^^ GPR rt ms
  | .ArithI (.XORI (_,rs,imm)) => GPR rs ms ^^^ imm.signExtend 64
  | .ArithR (.SUB (_,rs,rt)) => GPR rs ms - GPR rt ms
  | .ArithR (.AND (_,rs,rt)) => GPR rs ms &&& GPR rt ms
  | .Shift (.SRLI (_,rs,imm)) => GPR rs ms >>> imm.toNat
  | _ => 0
/-- Actual Run effect from original riscvOk; no target run is assumed. -/
theorem run_eq (i : instruction) (kind : Family i) (ms : riscv_state)
    (ok : riscvOk ms = true) :
    Run i ms = «write'GPR» (value i ms,destination i) ms := by
  have arch := ((riscvOk_iff ms).mp ok).2.1
  cases kind <;> simp [value,destination,Run,«dfn'XOR»,«dfn'XORI»,«dfn'SUB»,
    «dfn'AND»,«dfn'SRLI»,in32BitMode,curArch,architecture,MCSR,arch,GPR,gpr]
/-- Full native Next from actual encoded bytes and original validity. -/
theorem native_step (i : instruction) (kind : Family i) (ms : riscv_state)
    (rn : destination i ≠ 0#5) (ok : riscvOk ms = true)
    (bytes : encodedInstructionBytes ms i) :
    NextRISCV ms = some (constStep i ms) := by
  have lowbits : (Encode i).getLsbD 0 = true ∧ (Encode i).getLsbD 1 = true := by
    cases kind
    all_goals simp only [Encode,Rtype,Itype,opc,BitVec.setWidth_eq,BitVec.getLsbD_append]
    all_goals simp
  have decode : DecodeAny (.Word (Encode i)) = i := by
    cases kind
    · exact decode_encode_xor _ _ _
    · exact decode_encode_xori _ _ _
    · exact decode_encode_sub _ _ _
    · exact decode_encode_and _ _ _
    · exact decode_encode_srli _ _ _
  have updatedOk : riscvOk {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} = true := ok
  have run := run_eq i kind {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} updatedOk
  have val : value i {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} = value i ms := by
    cases kind <;> simp [value,GPR,gpr]
  rw [val] at run
  have next := write_next ms i (Encode i) (destination i) (value i ms) rn ok decode run
    lowbits.1 lowbits.2 bytes.1 bytes.2.1 bytes.2.2.1 bytes.2.2.2
  have pure := run_eq i kind ms ok
  simpa [constStep,pure,writePost,«write'GPR»,«write'gpr»,rn] using next
/-- Full Run frame, including every original projected machine field. -/
theorem run_frame (i : instruction) (kind : Family i)
    (ms : riscv_state) (ok : riscvOk ms = true) :
    (Run i ms).procID = ms.procID ∧ (Run i ms).c_PC = ms.c_PC ∧
    (Run i ms).MEM8 = ms.MEM8 ∧ (Run i ms).c_MCSR = ms.c_MCSR ∧
    (Run i ms).c_NextFetch = ms.c_NextFetch ∧ (Run i ms).exception = ms.exception := by
  rw [run_eq i kind ms ok]
  by_cases zero : destination i = 0#5 <;> simp [«write'GPR»,«write'gpr»,zero]
/-- Native Run congruence under the original full projection, including scratch31. -/
theorem run_projection (d : BitVec 64 → Prop) (i : instruction)
    (kind : Family i) (ms ns : riscv_state) (ok : riscvOk ms = true)
    (h : riscvProj d ms = riscvProj d ns) :
    riscvProj d (Run i ms) = riscvProj d (Run i ns) := by
  have okNs : riscvOk ns = true := (riscv_ok_of_projection_eq d ms ns h).symm.trans ok
  have fields := h
  simp only [riscvProj,Prod.mk.injEq] at fields
  have reads (r : BitVec 5) : GPR r ms = GPR r ns := by
    simp [GPR,gpr,fields.2.2.2.2.1]
  have vals : value i ms = value i ns := by
    cases kind <;> simp [value,reads]
  rw [run_eq i kind ms ok,run_eq i kind ns okNs,vals]
  by_cases zero : destination i = 0#5
  · simpa [«write'GPR»,zero] using h
  · simpa [riscvProj,«write'GPR»,«write'gpr»,holUpdate,zero] using
      ⟨fields.1,fields.2.1,fields.2.2.1,fields.2.2.2.1,
        congrArg (holUpdate (destination i) (value i ns)) fields.2.2.2.2.1,
        fields.2.2.2.2.2.1,fields.2.2.2.2.2.2⟩
theorem writePost_ok (ms : riscv_state) (rd : BitVec 5) (v : BitVec 64)
    (ok : riscvOk ms = true) : riscvOk (writePost ms rd v) = true := by
  have fields := (riscvOk_iff ms).mp ok
  apply (riscvOk_iff _).mpr
  simpa [writePost, holUpdate] using
    ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1,
      aligned_add_four _ fields.2.2.2.2⟩

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
infrastructure for full SubOverflow execution; no target execution is assumed. -/
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
proved per instruction above; full encoded-list assertions are assembled in the
parent SubOverflow counterpart module. -/
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

/-- SubOverflow-local composition infrastructure with no separately named HOL original. -/
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
infrastructure; original full encoder assertions are assembled separately in
the parent SubOverflow counterpart module. -/
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

end Flapjack.RiscV.TargetProof.SubOverflow
