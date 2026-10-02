import Flapjack.Compiler.Backend.LabToTarget.ShareMemState

namespace Flapjack.Test.LabToTargetShareMemStateParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget

/-! Kernel replay of `scripts/hol-probes/lab_to_target_share_mem_state_probe.out`: the satisfied
instance with no FFI names and the violated instance with one shared-memory name whose entry PC
is the halt PC. -/

-- smsr_nil=∀mc s1 t1 ms1. mc.ffi_names = [] ⇒ share_mem_state_rel mc s1 t1 ms1
example {labWidth : Nat} [NeZero labWidth] {width : Nat} [NeZero width] {γ δ F ε ζ : Type}
    (mc : MachineConfig width γ δ) (s1 : Flapjack.Compiler.Backend.LabSem.State labWidth Config F)
    (t1 : ε) (ms1 : ζ) : mc.ffiNames = [] → shareMemStateRel mc s1 t1 ms1 :=
  shareMemStateRel_nil mc s1 t1 ms1

-- smsr_halt=∀mc s1 t1 ms1 w. mc.ffi_names = [SharedMem MappedRead] ∧ mc.ffi_entry_pcs = [w] ∧ mc.halt_pc = w ⇒ ¬share_mem_state_rel mc s1 t1 ms1
example {labWidth : Nat} [NeZero labWidth] {width : Nat} [NeZero width] {γ δ F ε ζ : Type}
    (mc : MachineConfig width γ δ) (s1 : Flapjack.Compiler.Backend.LabSem.State labWidth Config F)
    (t1 : ε) (ms1 : ζ) (w : BitVec width) :
    mc.ffiNames = [HolFfiName.sharedMem .mappedRead] ∧ mc.ffiEntryPcs = [w] ∧ mc.haltPc = w →
      ¬ shareMemStateRel mc s1 t1 ms1 :=
  fun ⟨hn, he, hh⟩ => not_shareMemStateRel_halt mc s1 t1 ms1 w hn he hh

end Flapjack.Test.LabToTargetShareMemStateParity
