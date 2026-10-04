import Flapjack.RiscV.CorrectnessEncoding.RorStep
import Flapjack.RiscV.CorrectnessEncoding.ConstExecution

/-! Ror case-local native list composition, not a named HOL port.
The actual target iterator is reused unchanged. Every fetch/Next transition and
full interference/memory assertion follows from emitted bytes and original
validity; no target execution is assumed. Full Ror encoder cases remain open. -/
namespace Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.RiscV.Target
  Compiler.Encoders.AsmProps
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-- Whole complete-step list congruence with native PC advancement. Untagged
infrastructure for full Ror execution; no target execution is assumed. -/
theorem ror_step_list_projection_eq (d : BitVec 64 → Prop) (is : List instruction)
    (kinds : ∀ i ∈ is, RorInstruction i) (ms ns : riscv_state)
    (ok : riscvOk ms = true) (h : riscvProj d ms = riscvProj d ns) :
    riscvProj d (is.foldl (fun s i => rorStep i s) ms) =
      riscvProj d (is.foldl (fun s i => rorStep i s) ns) := by
  induction is generalizing ms ns with
  | nil => exact h
  | cons i is ih =>
    simp only [List.foldl_cons]
    exact ih (fun j hj => kinds j (List.mem_cons_of_mem i hj))
      (rorStep i ms) (rorStep i ns) (ror_step_ok i (kinds i (by simp)) ms ok)
      (ror_step_projection_eq d i (kinds i (by simp)) ms ns ok h)

/-- Interleave the original environment after each complete native Ror step.
This pure effect agrees with actual Next when its emitted bytes are present,
by `next_ror_step`; no encoded-list fetch/assertion assembly is claimed here. -/
noncomputable def rorStepInterleaved (env : Nat → riscv_state → riscv_state)
    (index : Nat) (is : List instruction) (ms : riscv_state) : riscv_state :=
  match is with
  | [] => ms
  | i :: tail => rorStepInterleaved env (index + 1) tail (env index (rorStep i ms))

/-- Arbitrary complete native step lists retain their full original projection
under original interference, including PC advancement and scratch31. Untagged
composition infrastructure; no target run or scratch-preservation premise. -/
theorem ror_interleaved_step_projection (d : BitVec 64 → Prop)
    (is : List instruction) (kinds : ∀ i ∈ is, RorInstruction i)
    (env : Nat → riscv_state → riscv_state) (index : Nat) (ms : riscv_state)
    (ok : riscvOk ms = true) (interference : interferenceOk env (riscvProj d)) :
    riscvProj d (rorStepInterleaved env index is ms) =
      riscvProj d (is.foldl (fun s i => rorStep i s) ms) := by
  induction is generalizing index ms with
  | nil => rfl
  | cons i is ih =>
    have kind := kinds i (by simp)
    have tailKinds : ∀ j ∈ is, RorInstruction j :=
      fun j hj => kinds j (List.mem_cons_of_mem i hj)
    have stepOk := ror_step_ok i kind ms ok
    have hEnv := interference index (rorStep i ms)
    have envOk : riscvOk (env index (rorStep i ms)) = true :=
      (riscv_ok_of_projection_eq d _ _ hEnv).trans stepOk
    simp only [rorStepInterleaved, List.foldl_cons]
    exact (ih tailKinds (index + 1) _ envOk).trans
      (ror_step_list_projection_eq d is tailKinds _ _ envOk hEnv)

/-- Complete pure-list native frame and total PC increment, for arbitrary
length and every intrinsic operand. The emitted-byte execution connection is
proved per instruction above; full encoded-list assertions remain open. -/
theorem ror_step_list_frame (is : List instruction)
    (kinds : ∀ i ∈ is, RorInstruction i) (ms : riscv_state)
    (ok : riscvOk ms = true) :
    let final := is.foldl (fun s i => rorStep i s) ms
    riscvOk final = true ∧ final.procID = ms.procID ∧ final.MEM8 = ms.MEM8 ∧
      final.c_PC final.procID = ms.c_PC ms.procID + BitVec.ofNat 64 (4 * is.length) := by
  induction is generalizing ms with
  | nil => simpa using ok
  | cons i is ih =>
    have kind := kinds i (by simp)
    have tailKinds : ∀ j ∈ is, RorInstruction j :=
      fun j hj => kinds j (List.mem_cons_of_mem i hj)
    have stepFrame := ror_step_frame i kind ms ok
    have tail := ih tailKinds (rorStep i ms) (ror_step_ok i kind ms ok)
    simp only [List.foldl_cons]
    refine ⟨tail.1, tail.2.1.trans stepFrame.1, tail.2.2.1.trans stepFrame.2.1, ?_⟩
    rw [tail.2.2.2, stepFrame.1, stepFrame.2.2]
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add]
    change ms.c_PC ms.procID + 4 + BitVec.ofNat 64 (4 * is.length) =
      ms.c_PC ms.procID + (BitVec.ofNat 64 (4 * is.length) + 4)
    rw [BitVec.add_assoc, BitVec.add_comm (4 : BitVec 64) (BitVec.ofNat 64 (4 * is.length))]

/-- Actual whole native execution follows the complete pure step list from
original emitted bytes and original projection-preserving interference.
All fetch, validity and remaining-byte premises are derived internally;
no target execution or post-state relation is an input. Untagged composition
infrastructure; the full original Ror assertions remain separate open work. -/
theorem ror_native_execute (d : BitVec 64 → Prop) (is : List instruction)
    (kinds : ∀ i ∈ is, RorInstruction i)
    (nonzero : ∀ i ∈ is, rorDestination i ≠ 0#5)
    (env : Nat → riscv_state → riscv_state) (index : Nat) (ms : riscv_state)
    (ok : riscvOk ms = true)
    (bytes : bytesInMemoryHOL (ms.c_PC ms.procID) (is.flatMap riscvEncode) ms.MEM8 d)
    (interference : interferenceOk env (riscvProj d)) :
    constNativeExecute env index is ms = rorStepInterleaved env index is ms := by
  induction is generalizing index ms with
  | nil => rfl
  | cons i is ih =>
    have kind := kinds i (by simp)
    have rn := nonzero i (by simp)
    have tailKinds : ∀ j ∈ is, RorInstruction j :=
      fun j hj => kinds j (List.mem_cons_of_mem i hj)
    have tailNonzero : ∀ j ∈ is, rorDestination j ≠ 0#5 :=
      fun j hj => nonzero j (List.mem_cons_of_mem i hj)
    simp only [List.flatMap_cons, bytesInMemory_append] at bytes
    have native := next_ror_step i kind ms rn ok (encoded_bytes_of_region d ms i bytes.1)
    have step : riscvTarget.next ms = rorStep i ms := by
      change holThe (NextRISCV ms) = _
      rw [native]
      simp [holThe]
    have frame := ror_step_frame i kind ms ok
    have stepOk := ror_step_ok i kind ms ok
    have envProjection := interference index (rorStep i ms)
    have envOk : riscvOk (env index (rorStep i ms)) = true :=
      (riscv_ok_of_projection_eq d _ _ envProjection).trans stepOk
    have tailBytes : bytesInMemoryHOL
        ((rorStep i ms).c_PC (rorStep i ms).procID)
        (is.flatMap riscvEncode) (rorStep i ms).MEM8 d := by
      simpa [frame.1, frame.2.1, frame.2.2, riscvEncode] using bytes.2
    have envBytes := bytes_projection_transfer d (rorStep i ms)
      (env index (rorStep i ms)) envProjection.symm _ _ tailBytes
    have pcEq : (env index (rorStep i ms)).c_PC (env index (rorStep i ms)).procID =
        (rorStep i ms).c_PC (rorStep i ms).procID := by
      have fields := envProjection
      simp only [riscvProj, Prod.mk.injEq] at fields
      exact fields.2.2.2.2.2.2
    rw [← pcEq] at envBytes
    simp only [constNativeExecute, rorStepInterleaved, step]
    exact ih tailKinds tailNonzero (index + 1) _ envOk envBytes

/-- Full original projection of actual native execution, derived from emitted
bytes, equals the complete pure-step list effect, including scratch31 and PC.
No target execution hypothesis; not a separately named HOL theorem. -/
theorem ror_native_execute_projection (d : BitVec 64 → Prop) (is : List instruction)
    (kinds : ∀ i ∈ is, RorInstruction i)
    (nonzero : ∀ i ∈ is, rorDestination i ≠ 0#5)
    (env : Nat → riscv_state → riscv_state) (index : Nat) (ms : riscv_state)
    (ok : riscvOk ms = true)
    (bytes : bytesInMemoryHOL (ms.c_PC ms.procID) (is.flatMap riscvEncode) ms.MEM8 d)
    (interference : interferenceOk env (riscvProj d)) :
    riscvProj d (constNativeExecute env index is ms) =
      riscvProj d (is.foldl (fun s i => rorStep i s) ms) := by
  rw [ror_native_execute d is kinds nonzero env index ms ok bytes interference]
  exact ror_interleaved_step_projection d is kinds env index ms ok interference

/-- Actual native list execution retains original validity, advances PC by
exactly four per instruction, and preserves every byte in the original domain.
The environment may change processor identity or memory outside that domain;
no stronger preservation premise is introduced. Untagged composition
infrastructure; original full encoder assertions remain separate open work. -/
theorem ror_native_execute_frame (d : BitVec 64 → Prop) (is : List instruction)
    (kinds : ∀ i ∈ is, RorInstruction i)
    (nonzero : ∀ i ∈ is, rorDestination i ≠ 0#5)
    (env : Nat → riscv_state → riscv_state) (index : Nat) (ms : riscv_state)
    (ok : riscvOk ms = true)
    (bytes : bytesInMemoryHOL (ms.c_PC ms.procID) (is.flatMap riscvEncode) ms.MEM8 d)
    (interference : interferenceOk env (riscvProj d)) :
    let final := constNativeExecute env index is ms
    riscvOk final = true ∧
      final.c_PC final.procID = ms.c_PC ms.procID + BitVec.ofNat 64 (4 * is.length) ∧
      ∀ a, d a → final.MEM8 a = ms.MEM8 a := by
  have pureFrame := ror_step_list_frame is kinds ms ok
  have projection := ror_native_execute_projection d is kinds nonzero env index ms ok bytes interference
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
theorem ror_native_asserts2 (d : BitVec 64 → Prop) (is : List instruction)
    (kinds : ∀ i ∈ is, RorInstruction i)
    (nonzero : ∀ i ∈ is, rorDestination i ≠ 0#5)
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
    have tailKinds : ∀ j ∈ is, RorInstruction j :=
      fun j hj => kinds j (List.mem_cons_of_mem i hj)
    have tailNonzero : ∀ j ∈ is, rorDestination j ≠ 0#5 :=
      fun j hj => nonzero j (List.mem_cons_of_mem i hj)
    simp only [List.flatMap_cons, bytesInMemory_append] at bytes
    have native := next_ror_step i kind ms rn ok (encoded_bytes_of_region d ms i bytes.1)
    have step : riscvTarget.next ms = rorStep i ms := by
      change holThe (NextRISCV ms) = _
      rw [native]
      simp [holThe]
    have frame := ror_step_frame i kind ms ok
    have stepOk := ror_step_ok i kind ms ok
    have envProjection := interference index (rorStep i ms)
    have envOk : riscvOk (env index (rorStep i ms)) = true :=
      (riscv_ok_of_projection_eq d _ _ envProjection).trans stepOk
    have tailBytes : bytesInMemoryHOL
        ((rorStep i ms).c_PC (rorStep i ms).procID)
        (is.flatMap riscvEncode) (rorStep i ms).MEM8 d := by
      simpa [frame.1, frame.2.1, frame.2.2, riscvEncode] using bytes.2
    have envBytes := bytes_projection_transfer d (rorStep i ms)
      (env index (rorStep i ms)) envProjection.symm _ _ tailBytes
    have pcEq : (env index (rorStep i ms)).c_PC (env index (rorStep i ms)).procID =
        (rorStep i ms).c_PC (rorStep i ms).procID := by
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

end Flapjack.RiscV.TargetProof
