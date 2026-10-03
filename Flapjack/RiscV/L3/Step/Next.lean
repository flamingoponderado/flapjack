import Flapjack.RiscV.L3.Step.Fetch
import Flapjack.RiscV.L3.Step.DecodeAny
import Flapjack.RiscV.L3.Step.UpdatePC
import Flapjack.RiscV.L3.Defs.Run

/-! Complete literal original riscv_step Next equation. This is the step theory's
NextRISCV, not a replacement for the model's stronger trap/interrupt dispatcher
or a compiler correctness theorem. Full Run inherits the rational-cut IEEE
assumption documented in SOUNDNESS item 8. -/
namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "NextRISCV_def"]
noncomputable def NextRISCV (s : riscv_state) : (Option riscv_state) :=
  (match (Fetch s) with | (f, s_1) => (let s : riscv_state := (Run (DecodeAny f) s_1); (if ((!(s.exception == exception.NoException))) then ((none : (Option riscv_state))) else ((let pc : (BitVec 64) := (PC s); (match (NextFetch s) with | none => (update_pc ((pc + (Skip s))) s) | some v1 => (match v1 with | .BranchTo a => (update_pc a ((«write'NextFetch» ((none : (Option TransferControl))) s))) | .Ereturn => (none : (Option riscv_state)) | .Mrts => (none : (Option riscv_state)) | .Trap _v5 => (none : (Option riscv_state)))))))))

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
