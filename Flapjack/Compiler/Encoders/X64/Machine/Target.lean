import Flapjack.Compiler.Encoders.X64.Machine.Execute
import Flapjack.Compiler.Encoders.AsmProps.Target
import Flapjack.HolArb

/-!
# The closed x86-64 `target` record

The record fields use `x64Config` for the already-ported source encoder and
`x64Next` for the closed machine step.  This is the x86-64 instance of the
generic `HolAsmTarget`, not a port of the full L3 `x64_step` model.  The
projection carries the architectural state the emitted subset touches: PC,
general-purpose registers, XMM registers, flags, the failure flag, and the
memory graph restricted to the source domain.
-/

namespace Flapjack.Compiler.Encoders.X64

open Flapjack Compiler.Encoders.Asm

local instance : Nonempty (HolAsmTarget 64 X64State X64Projection) :=
  ⟨{ config := x64Config,
     next := id,
     getPc := fun _ => 0,
     getReg := fun _ _ => 0,
     getFpReg := fun _ _ => 0,
     getByte := fun _ _ => 0,
     stateOk := fun _ => true,
     proj := fun _ _ => holArb X64Projection }⟩

/-- Closed x86-64 target record for the emitted instruction subset. -/
noncomputable def x64Target : HolAsmTarget 64 X64State X64Projection where
  config := x64Config
  next := x64Next
  getPc := fun s => s.pc
  getReg := fun s n => readReg s n
  getFpReg := fun s n => readXmm s n
  getByte := fun s a => s.mem a
  stateOk := x64StateOk
  proj := x64Proj

/-- Projection reductions used by the target-ok proof. -/
@[simp] theorem x64Target_next : x64Target.next = x64Next := rfl
@[simp] theorem x64Target_getPc : x64Target.getPc = (fun s => s.pc) := rfl
@[simp] theorem x64Target_getReg : x64Target.getReg = (fun s n => readReg s n) := rfl
@[simp] theorem x64Target_getFpReg : x64Target.getFpReg = (fun s n => readXmm s n) := rfl
@[simp] theorem x64Target_getByte : x64Target.getByte = (fun s a => s.mem a) := rfl
@[simp] theorem x64Target_stateOk : x64Target.stateOk = x64StateOk := rfl
@[simp] theorem x64Target_proj : x64Target.proj = x64Proj := rfl
@[simp] theorem x64Target_config : x64Target.config = x64Config := rfl

/-- Record projection regression. -/
theorem x64Target_projections :
    x64Target.next = x64Next ∧ x64Target.config = x64Config ∧
    x64Target.getPc = (fun s => s.pc) ∧
    x64Target.getReg = (fun s n => readReg s n) ∧
    x64Target.getFpReg = (fun s n => readXmm s n) ∧
    x64Target.getByte = (fun s a => s.mem a) ∧
    x64Target.stateOk = x64StateOk ∧ x64Target.proj = x64Proj := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Flapjack.Compiler.Encoders.X64
