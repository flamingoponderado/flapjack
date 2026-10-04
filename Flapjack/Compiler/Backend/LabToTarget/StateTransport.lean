import Flapjack.Compiler.Backend.LabToTarget.OracleTie
import Flapjack.Compiler.Backend.LabToTarget.StateRel

set_option autoImplicit false

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.Asm

/-- Full original oracle clock preservation. No field equality or resulting
oracle tie is assumed beyond the original complete pre-state tie. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem oracleTie_clock {width : Nat} [NeZero width] {S Q C : Type} {F : Type}
    (mc : MachineConfig width S Q) (ms : S)
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) (k : Nat)
    (h : oracleTie mc ms s) : oracleTie mc ms { s with clock := k } := h

/-- Full original state clock preservation, over the entire original tuple
and relation. This implication has exactly the original source direction.
The Lab state's configuration type is `Config` because the original
`state_rel_def` (lab_to_targetProofScript.sml:960) annotates its `s1` as
`('a,lab_to_target$config,'ffi) labSem$state`, which `state_rel_clock`
inherits; `oracleTie_clock` stays generic as `oracle_tie_def` (line 790) does. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stateRelClock {width : Nat} [NeZero width] {S Q : Type} {F : Type}
    (bundle : MachineConfig width S Q × LabSem.LabProgHOL width × Spt (Spt Nat) × BitVec width)
    (s : Flapjack.Compiler.Backend.LabSem.State width Config F)
    (t : AsmState width) (ms : S) (k : Nat)
    (h : stateRel bundle s t ms) : stateRel bundle { s with clock := k } t ms :=
  (stateRel_clock bundle s t ms k).mpr h

/-- Complete source shared-memory relation ignores only next_interfer.
Independent Lab/machine widths and the source's unused outer carriers remain
independent; literal total holEl and all FFI/MMIO obligations are preserved. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem shareMemStateRel_shiftInterfer {labWidth : Nat} [NeZero labWidth]
    {width : Nat} [NeZero width] {S Q : Type} {F : Type} {T M : Type}
    (mc : MachineConfig width S Q)
    (s : Flapjack.Compiler.Backend.LabSem.State labWidth Config F)
    (t : T) (ms : M) (l : Nat) (h : shareMemStateRel mc s t ms) :
    shareMemStateRel { mc with nextInterfer := fun i => mc.nextInterfer (i + l) }
      s t ms := h

/-- Full original domain/code relation shift. All code, total holEl lookups,
byte alignment and shared-address membership clauses remain unchanged. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem shareMemDomainCodeRel_shiftInterfer {width : Nat} [NeZero width]
    {S Q C : Type} {F : Type}
    (mc : MachineConfig width S Q) (p : BitVec width) (code : LabSem.LabProgHOL width)
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) (l : Nat)
    (h : shareMemDomainCodeRel mc p code (fun a => s.sharedMemDomain a = true)) :
    shareMemDomainCodeRel { mc with nextInterfer := fun i => mc.nextInterfer (i + l) }
      p code (fun a => s.sharedMemDomain a = true) := h

/-- Full original state relation shift. Only the actual machine interference
sequence changes; all original FFI/cache/shared-memory contracts and code and
memory conditions must follow from the complete pre-state relation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stateRel_shiftInterfer {width : Nat} [NeZero width] {S Q : Type} {F : Type}
    (mc : MachineConfig width S Q) (code : LabSem.LabProgHOL width) (labs : Spt (Spt Nat))
    (p : BitVec width) (s : Flapjack.Compiler.Backend.LabSem.State width Config F)
    (t : AsmState width) (ms : S) (l : Nat)
    (h : stateRel (mc, code, labs, p) s t ms) :
    stateRel (shiftInterfer l mc, code, labs, p) s t ms := by
  exact ⟨h.1,
    h.2.1,
    h.2.2.1,
    h.2.2.2.1,
    h.2.2.2.2.1,
    h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    (fun i ms => h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (i + l) ms),
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Full-state composition consumer of the two source shifts. Flapjack
infrastructure: HOL names only the single-shift law, not this combination. -/
theorem stateRel_shiftInterfer_twice {width : Nat} [NeZero width] {S Q : Type} {F : Type}
    (mc : MachineConfig width S Q) (code : LabSem.LabProgHOL width) (labs : Spt (Spt Nat))
    (p : BitVec width) (s : Flapjack.Compiler.Backend.LabSem.State width Config F)
    (t : AsmState width) (ms : S) (a b : Nat)
    (h : stateRel (mc, code, labs, p) s t ms) :
    stateRel (shiftInterfer (a + b) mc, code, labs, p) s t ms := by
  have h1 := stateRel_shiftInterfer mc code labs p s t ms b h
  have h2 := stateRel_shiftInterfer (shiftInterfer b mc) code labs p s t ms a h1
  simpa only [shiftInterfer_intro] using h2

end Flapjack.Compiler.Backend.LabToTarget
