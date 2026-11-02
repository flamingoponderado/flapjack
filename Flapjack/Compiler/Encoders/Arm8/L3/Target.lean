import Flapjack.Compiler.Encoders.Arm8.L3.Types
import Flapjack.Compiler.Encoders.Arm8.L3.Defs
import Flapjack.Compiler.Encoders.Arm8.Machine.State
import Flapjack.Misc.Alignment
import Flapjack.Misc.SetSep
import Flapjack.Misc.Option

/-!
# L3 ARMv8 target: projection, validity gate, and the closed-model link

Counterparts of CakeML's `arm8_proj` and `arm8_ok`
(`cakeml/compiler/encoders/arm8/arm8_targetScript.sml`, lines 343-353), stated
over the L3 `arm8_state` carrier of `Flapjack/Compiler/Encoders/Arm8/L3/Types.lean`
rather than the closed `Arm8State`.  The L3 `arm8_next`/`arm8_target` pair is
*not* ported here: `arm8_next = THE o NextStateARM8` needs the pinned L3
transition semantics (`Next`/`Fetch`/`Decode`/`Run` in
`HOL/examples/l3-machine-code/arm8/model/arm8Script.sml`), which is the
remaining work of issue #1239.

The final theorem links the closed model's validity condition to the L3 gate:
under `arm8StateRel`, the closed `arm8StateOk` implies L3 `arm8_ok`, with the
L3-only control-register, privilege and exception fields supplied as explicit
hypotheses because the closed carrier does not model them.  It is a
validity-condition refinement only; it does not refine transitions and does not
establish HOL-to-Lean semantic equivalence.
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
step, projected with `THE`.  This is the transition over the L3 carrier; the
`arm8_target` record and the encoder-correctness chain still need the full L3
`arm8_config` carrier (#1229) and the simulation proofs (#1239). -/
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

/-- Flapjack relation between the closed `Arm8State` and the L3 `arm8_state` on
the fields the closed model does model: PC, the four flags, the 31 general
registers (L3 register 31 is zero), and the byte memory.  The L3-only fields
(`EL`, `SCTLR_EL1`, `TCR_EL1`, `exception`, `SP_EL*`, `branch_hint`) are not
constrained here; `arm8Ok_of_closed` takes the ones `arm8_ok` reads as explicit
hypotheses.  No HOL original. -/
def arm8StateRel (ms : Arm8State) (l3 : arm8_state) : Prop :=
  l3.PC = ms.pc ∧
  l3.PSTATE.N = ms.n ∧
  l3.PSTATE.Z = ms.z ∧
  l3.PSTATE.C = ms.c ∧
  l3.PSTATE.V = ms.v ∧
  (∀ r : BitVec 5, l3.REG r = if r.toNat = 31 then 0 else ms.regs r.toNat) ∧
  (∀ a : BitVec 64, l3.MEM a = ms.mem a)

/-- The closed model's validity condition implies CakeML's L3 `arm8_ok` on the
related L3 state, given the L3-only configuration fields that the closed
carrier does not model.  Flapjack infrastructure (no HOL original): it relates
the closed model to the L3 validity gate, not to the L3 transition semantics,
and it is not a HOL-to-Lean equivalence claim. -/
theorem arm8Ok_of_closed (ms : Arm8State) (l3 : arm8_state)
    (hrel : arm8StateRel ms l3)
    (hEL : l3.PSTATE.EL = 0)
    (hE0E : l3.SCTLR_EL1.E0E = false)
    (hSA0 : l3.SCTLR_EL1.SA0 = false)
    (hTBI1 : l3.TCR_EL1.TBI1 = false)
    (hTBI0 : l3.TCR_EL1.TBI0 = false)
    (hExc : l3.exception = exception.NoException)
    (hok : arm8StateOk ms = true) :
    arm8Ok l3 = true := by
  rcases hrel with ⟨hPC, _, _, _, _, _, _⟩
  have hal : holAligned 2 ms.pc = true := by
    have h := hok
    simp only [arm8StateOk, Bool.and_eq_true] at h
    exact h.1
  rw [← hPC] at hal
  simp [arm8Ok, hEL, hE0E, hSA0, hTBI1, hTBI0, hExc, hal]

end Flapjack.Compiler.Encoders.Arm8.L3
