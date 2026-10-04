import Flapjack.RiscV.L3.Step.Fetch
import Flapjack.RiscV.L3.Step.DecodeAny
import Flapjack.RiscV.L3.Step.UpdatePC
import Flapjack.RiscV.L3.Defs.Run

/-! RV64IM instruction step with branch control and synchronous errors. -/
namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3

noncomputable def NextRISCV (s : riscv_state) : (Option riscv_state) :=
  (match (Fetch s) with | (f, s_1) => (let s : riscv_state := (Run (DecodeAny f) s_1); (if ((!(s.exception == exception.NoException))) then ((none : (Option riscv_state))) else ((let pc : (BitVec 64) := (PC s); (match (NextFetch s) with | none => (update_pc ((pc + (Skip s))) s) | some v1 => (match v1 with | .BranchTo a => (update_pc a ((«write'NextFetch» ((none : (Option TransferControl))) s))) | .Trap _v5 => (none : (Option riscv_state)))))))))

-- Keep reviewed interpreter calls and state-projection matches opaque while
-- checking this outer equation; the proof splits their complete result carriers.
attribute [local irreducible] Run Fetch DecodeAny update_pc NextFetch

/-- Flapjack full source-equation regression, with no successful fetch/run,
accepted opcode, mode or state restriction. No distinct named HOL theorem. -/
theorem NextRISCV_equation (s : riscv_state) :
    NextRISCV s =
      let (f, s) := Fetch s
      let s := Run (DecodeAny f) s
      if s.exception != exception.NoException then none else
        let pc := PC s
        match NextFetch s with
        | none => update_pc (pc + Skip s) s
        | some (.BranchTo a) => update_pc a («write'NextFetch» none s)
        | _ => none := by
  unfold NextRISCV
  cases hfetch : Fetch s with
  | mk f fetched =>
    dsimp only
    generalize hrun : Run (DecodeAny f) fetched = post
    cases hcontrol : NextFetch post with
    | none => rfl
    | some control => cases control <;> rfl

end Flapjack.RiscV.L3.Step
