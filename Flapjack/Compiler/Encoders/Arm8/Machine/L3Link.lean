module

public import Flapjack.Compiler.Encoders.Arm8.L3.Target
public import Flapjack.Compiler.Encoders.Arm8.Machine.State

@[expose] public section

/-!
# The closed-model validity link to the L3 gate

The closed model's validity predicate `arm8StateOk` implies CakeML's L3
`arm8_ok` on a related L3 state.  These declarations mention the closed
`Arm8State` carrier, so they live on the closed-model side: the L3 tree
(`L3/Target.lean` and the encoder-correctness cases) does not import
`Machine/`.  This is Flapjack infrastructure (no HOL original); it relates the
closed model to the L3 validity gate, not to the L3 transition semantics.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8

/-- Flapjack relation between the closed `Arm8State` and the L3 `arm8_state` on
the fields the closed model does model: PC, the four flags, the general
registers below 31, and the byte memory.  L3's `REG` is a stored map with no
zero-register invariant -- only the `X` read function returns zero for index 31
-- so the stored `REG 31` is left unconstrained.  The L3-only fields (`EL`,
`SCTLR_EL1`, `TCR_EL1`, `exception`, `SP_EL*`, `branch_hint`) are not
constrained here either; `arm8Ok_of_closed` takes the ones `arm8_ok` reads as
explicit hypotheses.  No HOL original. -/
def arm8StateRel (ms : Arm8State) (l3 : arm8_state) : Prop :=
  l3.PC = ms.pc ∧
  l3.PSTATE.N = ms.n ∧
  l3.PSTATE.Z = ms.z ∧
  l3.PSTATE.C = ms.c ∧
  l3.PSTATE.V = ms.v ∧
  (∀ r : BitVec 5, r.toNat < 31 → l3.REG r = ms.regs r.toNat) ∧
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
