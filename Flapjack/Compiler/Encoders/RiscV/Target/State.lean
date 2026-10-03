import Flapjack.Compiler.Encoders.RiscV.Target.Configuration
import Flapjack.Compiler.Encoders.AsmProps.Target
import Flapjack.RiscV.L3.Step.Next
import Flapjack.Misc.Alignment
import Flapjack.Misc.SetSep

/-! Full native target state definitions. Failed `THE` uses the reviewed
canonical unspecified value. HOL omits `get_fp_reg` in the record constructor;
its field is projected from the canonical arbitrary whole target record,
not independently chosen as an arbitrary function or zero-filled. -/
namespace Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack RiscV.L3

@[hol "cakeml/compiler/encoders/riscv/riscv_targetScript.sml" "riscv_next_def"]
noncomputable def riscvNext (s : riscv_state) : riscv_state :=
  holThe (RiscV.L3.Step.NextRISCV s)

@[hol "cakeml/compiler/encoders/riscv/riscv_targetScript.sml" "riscv_ok_def"]
def riscvOk (s : riscv_state) : Bool :=
  ((s.c_MCSR s.procID).mstatus.VM == 0) &&
  ((s.c_MCSR s.procID).mcpuid.ArchBase == 2) &&
  (s.c_NextFetch s.procID == none) &&
  (s.exception == exception.NoException) && holAligned 2 (s.c_PC s.procID)

/-- Flapjack naming infrastructure for the literal seven-component HOL tuple;
no independent original declaration or extra validity restriction. -/
abbrev RiscVProjection := BitVec 5 × BitVec 2 × Option TransferControl ×
  exception × (BitVec 5 → BitVec 64) × ((BitVec 64 × BitVec 8) → Prop) × BitVec 64

@[hol "cakeml/compiler/encoders/riscv/riscv_targetScript.sml" "riscv_proj_def"]
def riscvProj (d : BitVec 64 → Prop) (s : riscv_state) : RiscVProjection :=
  ((s.c_MCSR s.procID).mstatus.VM,
   (s.c_MCSR s.procID).mcpuid.ArchBase,
   s.c_NextFetch s.procID,
   s.exception,
   s.c_gpr s.procID,
   SetSep.fun2Set (s.MEM8, d),
   s.c_PC s.procID)

-- This record proves the HOL carrier is nonempty; it is not the value chosen
-- by holArb and does not specify any omitted field of riscvTarget.
local instance : Nonempty (HolAsmTarget 64 riscv_state RiscVProjection) :=
  ⟨{ config := riscvConfig, next := id, getPc := fun _ => 0,
     getReg := fun _ _ => 0, getFpReg := fun _ _ => 0,
     getByte := fun _ _ => 0, stateOk := fun _ => true,
     proj := riscvProj }⟩

@[hol "cakeml/compiler/encoders/riscv/riscv_targetScript.sml" "riscv_target_def"]
noncomputable def riscvTarget : HolAsmTarget 64 riscv_state RiscVProjection where
  next := riscvNext
  config := riscvConfig
  getPc := fun s => s.c_PC s.procID
  getReg := fun s n => s.c_gpr s.procID (BitVec.ofNat 5 n)
  getFpReg := (holArb (HolAsmTarget 64 riscv_state RiscVProjection)).getFpReg
  getByte := riscv_state.MEM8
  stateOk := riscvOk
  proj := riscvProj

/-- Flapjack source-review regression of all five original validity conjuncts;
no extra native-state or successful-step premise. -/
theorem riscvOk_iff (s : riscv_state) :
    riscvOk s = true ↔
    (s.c_MCSR s.procID).mstatus.VM = 0 ∧
    (s.c_MCSR s.procID).mcpuid.ArchBase = 2 ∧
    s.c_NextFetch s.procID = none ∧
    s.exception = exception.NoException ∧ holAligned 2 (s.c_PC s.procID) = true := by
  simp [riscvOk, Bool.and_eq_true, and_assoc]

/-- Flapjack memory-graph membership regression retaining the full domain. -/
theorem riscvProj_memory (d : BitVec 64 → Prop) (s : riscv_state)
    (a : BitVec 64) (b : BitVec 8) :
    (riscvProj d s).2.2.2.2.2.1 (a, b) ↔ s.MEM8 a = b ∧ d a := by
  exact SetSep.fun2SetThm s.MEM8 d a b

/-- Full record projection regression; Flapjack-specific equation, not a
separate HOL theorem or a successful-target-step assumption. -/
theorem riscvTarget_projections :
    riscvTarget.next = riscvNext ∧ riscvTarget.config = riscvConfig ∧
    riscvTarget.getPc = (fun s => s.c_PC s.procID) ∧
    riscvTarget.getReg = (fun s n => s.c_gpr s.procID (BitVec.ofNat 5 n)) ∧
    riscvTarget.getFpReg = (holArb (HolAsmTarget 64 riscv_state RiscVProjection)).getFpReg ∧
    riscvTarget.getByte = riscv_state.MEM8 ∧
    riscvTarget.stateOk = riscvOk ∧ riscvTarget.proj = riscvProj := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Flapjack.Compiler.Encoders.RiscV.Target
