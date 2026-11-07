module

public import Flapjack.Misc.Sptree
public import Flapjack.HolRef
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace Flapjack.Compiler.Backend.X64Config

/-- CakeML's x86-64 register names (`x64_names`, `x64_configScript.sml:10-28`):
stack-language register `k` is machine register `x64NameLookup k`.

Source 0 is RAX, 1 RCX, 2 RDX, 3 RBX, 4 RSP, 5 RBP, 6 RSI, 7 RDI, 8-15 R8-R15.
The mapping passes arguments 1-6 in RDI, RSI, RDX, RCX, R8, R9, and makes
registers 11-13 callee-saved in R14, R13, R12.  Registers 4 (RSP) and 5 (RBP)
are avoided by `x64_config`'s `avoid_regs`. -/
@[hol "cakeml/compiler/backend/x64/x64_configScript.sml" "x64_names_def" 10]
def x64Names : Flapjack.Spt Nat :=
  Flapjack.sptInsert 1 7 (Flapjack.sptInsert 2 6 (Flapjack.sptInsert 3 2
    (Flapjack.sptInsert 4 1 (Flapjack.sptInsert 5 8 (Flapjack.sptInsert 6 9
    (Flapjack.sptInsert 11 14 (Flapjack.sptInsert 12 13 (Flapjack.sptInsert 13 12
    (Flapjack.sptInsert 7 3 (Flapjack.sptInsert 8 15 (Flapjack.sptInsert 9 11
    (Flapjack.sptInsert 14 4 (Flapjack.sptInsert 15 5 .ln)))))))))))))

/-- Identity-default lookup in `x64Names` (Flapjack infrastructure). -/
def x64NameLookup (register : Nat) : Nat :=
  (Flapjack.sptLookup register x64Names).getD register

/-- `x64Names` as an explicit function (Flapjack infrastructure for deciding
facts about the names). -/
def x64NameMap (register : Nat) : Nat :=
  match register with
  | 1 => 7 | 2 => 6 | 3 => 2 | 4 => 1 | 5 => 8 | 6 => 9 | 11 => 14 | 12 => 13
  | 13 => 12 | 7 => 3 | 8 => 15 | 9 => 11 | 14 => 4 | 15 => 5
  | r => r

theorem x64Names_lookup_eq (register : Nat) :
    (Flapjack.sptLookup register x64Names).getD register = x64NameMap register := by
  by_cases h : register < 16
  · interval_cases register <;>
      simp [x64Names, Flapjack.sptInsert, Flapjack.sptLookup, x64NameMap]
  · have hnone : Flapjack.sptLookup register x64Names = none := by
      unfold x64Names
      repeat rw [Flapjack.sptLookup_sptInsert_ne _ _ _ _ (by omega)]
      rfl
    rw [hnone]
    unfold x64NameMap
    split <;> first | rfl | omega

end Flapjack.Compiler.Backend.X64Config
