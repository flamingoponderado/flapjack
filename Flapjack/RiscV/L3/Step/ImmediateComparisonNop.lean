import Flapjack.RiscV.L3.Defs.SetLess

namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3
set_option autoImplicit false

/-- Local derivation of the original step evaluator's mode rewrite. The
ArchBase exclusion is an original SLTI/SLTIU hypothesis, propagated by HOL's
not1 and in32BitMode EV. This helper claims no separately exported original. -/
private theorem comparison_mode (s : riscv_state)
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

/-- Original generated SLTI_NOP companion at source839. Both original
hypotheses are retained: destination zero and ArchBase exclusion. The entire
native state is unchanged, with arbitrary source register and immediate.
Only word/register/mode operations occur; no real arithmetic assumption. -/
@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SLTI_NOP"]
theorem dfnSltINop (rd rs1 : BitVec 5) (imm : BitVec 12) (s : riscv_state)
    (h : rd = 0#5) (arch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1#2) :
    «dfn'SLTI» (rd, rs1, imm) s = s := by
  subst rd
  simp only [«dfn'SLTI», comparison_mode s arch]
  simp [«write'GPR»]

/-- Original generated SLTIU_NOP companion at source840, with the same two
original hypotheses and unrestricted word5 source/word12 immediate. Whole
native state equality is retained; no real arithmetic assumption. -/
@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SLTIU_NOP"]
theorem dfnSltIUNop (rd rs1 : BitVec 5) (imm : BitVec 12) (s : riscv_state)
    (h : rd = 0#5) (arch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1#2) :
    «dfn'SLTIU» (rd, rs1, imm) s = s := by
  subst rd
  simp only [«dfn'SLTIU», comparison_mode s arch]
  simp [«write'GPR»]

end Flapjack.RiscV.L3.Step
