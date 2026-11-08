import Flapjack.RiscV.L3.Defs.SetLess

/-! Shared mode rewrite of the original SLT/SLTU/SLTI/SLTIU step evaluators.
The ArchBase exclusion is an original hypothesis, propagated by HOL's not1 and
in32BitMode EV. This helper claims no separately named HOL original. -/
namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3
set_option autoImplicit false

/-- Mode rewrite under the original ArchBase exclusion, shared by the register
and immediate comparison equations. -/
theorem comparison_mode (s : riscv_state)
    (h : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1#2) :
    in32BitMode () s = ((s.c_MCSR s.procID).mcpuid.ArchBase == 0#2, s) := by
  let ab := (s.c_MCSR s.procID).mcpuid.ArchBase
  have bound : ab.toNat < 4 := ab.isLt
  have neq : ab.toNat ≠ 1 := by
    intro e
    apply h
    apply BitVec.eq_of_toNat_eq
    exact e
  have choices : ab.toNat = 0 ∨ ab.toNat = 2 ∨ ab.toNat = 3 := by omega
  rcases choices with e | e | e
  all_goals
    have eq := BitVec.ofNat_toNat 2 ab
    rw [e] at eq
    have eq' := eq.symm
    simp only [BitVec.setWidth_eq, ab] at eq'
    simp [in32BitMode, curArch, architecture, MCSR, eq']

end Flapjack.RiscV.L3.Step
