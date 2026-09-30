import Flapjack.Compiler.Backend.RiscVConfig.Names
import Flapjack.RiscV.RegisterMap
import Flapjack.HolRef

namespace Flapjack.Compiler.Backend.RiscVConfig

/-- Flapjack execution correspondence, not a separate HOL declaration:
identity-default lookup in the exact Spt equals the existing concrete mapper
for every natural register, including names outside the architecture range. -/
@[simp] theorem riscvNames_lookup_eq (register : Nat) :
    (Flapjack.sptLookup register riscvNames).getD register =
      Flapjack.RiscV.riscvRegisterName register := by
  by_cases h : register ≤ 30
  · have hcases : register = 0 ∨ register = 1 ∨ register = 2 ∨ register = 3 ∨ register = 4 ∨ register = 5 ∨ register = 6 ∨ register = 7 ∨ register = 8 ∨ register = 9 ∨ register = 10 ∨ register = 11 ∨ register = 12 ∨ register = 13 ∨ register = 14 ∨ register = 15 ∨ register = 16 ∨ register = 17 ∨ register = 18 ∨ register = 19 ∨ register = 20 ∨ register = 21 ∨ register = 22 ∨ register = 23 ∨ register = 24 ∨ register = 25 ∨ register = 26 ∨ register = 27 ∨ register = 28 ∨ register = 29 ∨ register = 30 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [riscvNames, Flapjack.sptInsert, Flapjack.sptLookup, Flapjack.RiscV.riscvRegisterName]
  · have hlarge : 32 ≤ register ∨ register = 31 := by omega
    have hnone : Flapjack.sptLookup register riscvNames = none := by
      unfold riscvNames
      repeat rw [Flapjack.sptLookup_sptInsert_ne _ _ _ _ (by omega)]
      rfl
    rw [hnone]
    rcases hlarge with hlarge | rfl
    · exact (Flapjack.RiscV.riscvRegisterName_id_of_ge_32 hlarge).symm
    · rfl

@[simp] theorem riscvNameLookup_eq (register : Nat) :
    riscvNameLookup register = Flapjack.RiscV.riscvRegisterName register :=
  riscvNames_lookup_eq register

end Flapjack.Compiler.Backend.RiscVConfig
