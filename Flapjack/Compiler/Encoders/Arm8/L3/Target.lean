import Flapjack.Compiler.Encoders.Arm8.L3.Types
import Flapjack.Compiler.Encoders.Arm8.L3.Defs
import Flapjack.Misc.Alignment
import Flapjack.Misc.SetSep
import Flapjack.Misc.Option

/-!
# L3 ARMv8 target: projection, validity gate, and the closed-model link

Counterparts of CakeML's `arm8_proj` and `arm8_ok`
(`cakeml/compiler/encoders/arm8/arm8_targetScript.sml`: `arm8_ok_def` at line
20, `arm8_proj_def` at line 343), stated
over the L3 `arm8_state` carrier of `Flapjack/Compiler/Encoders/Arm8/L3/Types.lean`
rather than the closed `Arm8State`.  `arm8_next = THE o NextStateARM8` is
stated here over the L3 carrier, using the rendered `NextStateARM8` closure of
`L3/Defs.lean`; the `arm8_target` record is `arm8TargetL3` in
`Flapjack/Compiler/Encoders/Arm8/L3/Target/State.lean`, the exact
`arm8_target_def` instance over the L3 `arm8_config` carrier (`arm8ConfigL3`,
`L3/Configuration.lean`).  The per-instruction simulation proofs are the tagged
`arm8_encoder_correct` case theorems in `L3/CorrectnessEncoding/`, assembled as
`arm8EncoderCorrectL3`.

The link between the closed model's validity condition and the L3 gate (under
`arm8StateRel`, the closed `arm8StateOk` implies L3 `arm8_ok`) lives on the
closed-model side in `Machine/L3Link.lean`, so this module does not import
`Machine/`.  That link is a validity-condition refinement only; it does not
refine transitions and does not establish HOL-to-Lean semantic equivalence.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8

/-- The literal seven-component tuple of CakeML's `arm8_proj` (Flapjack naming
infrastructure; no independent HOL declaration). -/
abbrev Arm8L3Projection := ProcState × SCTLRType × TCR_EL1 × exception ×
  (BitVec 5 → BitVec 64) × ((BitVec 64 × BitVec 8) → Prop) × BitVec 64

/-- CakeML's `arm8_proj` (`arm8_targetScript.sml:343-346`): the projected
machine state, with the memory graph restricted to the source domain. -/
@[hol "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_proj_def"]
def arm8Proj (d : BitVec 64 → Prop) (s : arm8_state) : Arm8L3Projection :=
  (s.PSTATE, s.SCTLR_EL1, s.TCR_EL1, s.exception, s.REG,
   SetSep.fun2Set (s.MEM, d), s.PC)

/-- CakeML's `arm8_ok` (`arm8_targetScript.sml:20-27`): exception level zero,
no E0E/SA0 trapping, no TBI, no pending exception, and an aligned PC. -/
@[hol "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_ok_def"]
def arm8Ok (s : arm8_state) : Bool :=
  decide (s.PSTATE.EL = 0) && !s.SCTLR_EL1.E0E && !s.SCTLR_EL1.SA0 &&
  !s.TCR_EL1.TBI1 && !s.TCR_EL1.TBI0 &&
  decide (s.exception = exception.NoException) && holAligned 2 s.PC

/-- CakeML's `arm8_next` (`arm8_targetScript.sml:15`): the L3 `NextStateARM8`
step, projected with `THE`.  This is the transition over the L3 carrier;
`arm8TargetL3` (`L3/Target/State.lean`) is the exact `arm8_target_def` instance
that uses it, and `arm8EncoderCorrectL3` assembles the tagged per-instruction
cases over it. -/
@[hol "cakeml/compiler/encoders/arm8/arm8_targetScript.sml" "arm8_next_def"]
noncomputable def arm8Next (s : arm8_state) : arm8_state :=
  holThe (NextStateARM8 s)

/-- Flapjack source-review regression of all seven original validity conjuncts;
no extra native-state or successful-step premise. -/
theorem arm8Ok_iff (s : arm8_state) :
    arm8Ok s = true ↔
    s.PSTATE.EL = 0 ∧
    s.SCTLR_EL1.E0E = false ∧
    s.SCTLR_EL1.SA0 = false ∧
    s.TCR_EL1.TBI1 = false ∧
    s.TCR_EL1.TBI0 = false ∧
    s.exception = exception.NoException ∧
    holAligned 2 s.PC = true := by
  simp [arm8Ok, Bool.and_eq_true, and_assoc]

/-- Flapjack memory-graph membership regression retaining the full domain. -/
theorem arm8Proj_memory (d : BitVec 64 → Prop) (s : arm8_state)
    (a : BitVec 64) (b : BitVec 8) :
    (arm8Proj d s).2.2.2.2.2.1 (a, b) ↔ s.MEM a = b ∧ d a := by
  exact SetSep.fun2SetThm s.MEM d a b

end Flapjack.Compiler.Encoders.Arm8.L3
