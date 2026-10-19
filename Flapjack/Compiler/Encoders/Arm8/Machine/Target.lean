import Flapjack.Compiler.Encoders.Arm8.Machine.Execute
import Flapjack.Compiler.Encoders.Arm8.Configuration
import Flapjack.Compiler.Encoders.AsmProps.Target
import Flapjack.HolArb

/-!
# The closed ARMv8 `target` record

The record fields use `arm8Config` for the already-ported source encoder and
`arm8Next` for the closed machine step above.  This is the ARM8 instance of the
generic `HolAsmTarget`, not a port of the full L3 `arm8_step` model.
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm

local instance : Nonempty (HolAsmTarget 64 Arm8State Arm8Projection) :=
  ⟨{ config := arm8Config,
     next := id,
     getPc := fun _ => 0,
     getReg := fun _ _ => 0,
     getFpReg := fun _ _ => 0,
     getByte := fun _ _ => 0,
     stateOk := fun _ => true,
     proj := fun _ _ => holArb Arm8Projection }⟩

/-- Closed ARMv8 target record for the emitted instruction subset. -/
noncomputable def arm8Target : HolAsmTarget 64 Arm8State Arm8Projection where
  config := arm8Config
  next := arm8Next
  getPc := fun s => s.pc
  getReg := fun s n => s.regs n
  getFpReg := (holArb (HolAsmTarget 64 Arm8State Arm8Projection)).getFpReg
  getByte := fun s a => s.mem a
  stateOk := arm8StateOk
  proj := arm8Proj

/-- Record projection regression. -/
theorem arm8Target_projections :
    arm8Target.next = arm8Next ∧ arm8Target.config = arm8Config ∧
    arm8Target.getPc = (fun s => s.pc) ∧
    arm8Target.getReg = (fun s n => s.regs n) ∧
    arm8Target.getFpReg =
      (holArb (HolAsmTarget 64 Arm8State Arm8Projection)).getFpReg ∧
    arm8Target.getByte = (fun s a => s.mem a) ∧
    arm8Target.stateOk = arm8StateOk ∧ arm8Target.proj = arm8Proj := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Projection reductions used by the target-ok proof. -/
@[simp] theorem arm8Target_getPc : arm8Target.getPc = (fun s => s.pc) := rfl
@[simp] theorem arm8Target_getReg : arm8Target.getReg = (fun s n => s.regs n) := rfl
@[simp] theorem arm8Target_getFpReg : arm8Target.getFpReg =
    (holArb (HolAsmTarget 64 Arm8State Arm8Projection)).getFpReg := rfl
@[simp] theorem arm8Target_getByte : arm8Target.getByte = (fun s a => s.mem a) := rfl
@[simp] theorem arm8Target_stateOk : arm8Target.stateOk = arm8StateOk := rfl
@[simp] theorem arm8Target_proj : arm8Target.proj = arm8Proj := rfl
@[simp] theorem arm8Target_config : arm8Target.config = arm8Config := rfl

end Flapjack.Compiler.Encoders.Arm8
