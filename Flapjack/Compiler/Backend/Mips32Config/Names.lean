import Flapjack.Misc.Sptree
import Flapjack.HolRef
import Mathlib.Tactic.IntervalCases

namespace Flapjack.Compiler.Backend.Mips32Config

/-- CakeML's MIPS register names: stack-language register `k` is machine register
`mips32NameLookup k`. Source registers 1-4 are the argument registers `$a0`-`$a3`, source 0
is `$ra`, and the encoder temporaries `$at`/`$fp`, `$zero`, `$sp`, `$gp`, `$k0`/`$k1` and
`$t9` are avoided. The MIPS32 backend reuses the map unchanged: the MIPS32 calling registers
are the same as MIPS64's. -/
@[hol "cakeml/compiler/backend/mips/mips_configScript.sml" "mips_names_def" 10]
def mipsNames : Flapjack.Spt Nat :=
  Flapjack.sptInsert 0 31 (Flapjack.sptInsert 1 4 (Flapjack.sptInsert 2 5
    (Flapjack.sptInsert 3 6 (Flapjack.sptInsert 4 7 (Flapjack.sptInsert 7 2
    (Flapjack.sptInsert 5 24 (Flapjack.sptInsert 6 3 (Flapjack.sptInsert 24 0
    (Flapjack.sptInsert 31 1 .ln)))))))))

/-- Identity-default lookup in `mipsNames` (Flapjack infrastructure). -/
def mips32NameLookup (register : Nat) : Nat :=
  (Flapjack.sptLookup register mipsNames).getD register

end Flapjack.Compiler.Backend.Mips32Config

namespace Flapjack.Compiler.Backend.Mips32Config

/-- `mipsNames` as an explicit function (Flapjack infrastructure for deciding facts about
the names). -/
def mipsNameMap (register : Nat) : Nat :=
  match register with
  | 0 => 31 | 1 => 4 | 2 => 5 | 3 => 6 | 4 => 7 | 5 => 24 | 6 => 3 | 7 => 2 | 24 => 0
  | 31 => 1 | r => r

theorem mipsNames_lookup_eq (register : Nat) :
    (Flapjack.sptLookup register mipsNames).getD register = mipsNameMap register := by
  by_cases h : register < 32
  · interval_cases register <;>
      simp [mipsNames, Flapjack.sptInsert, Flapjack.sptLookup, mipsNameMap]
  · have hnone : Flapjack.sptLookup register mipsNames = none := by
      unfold mipsNames
      repeat rw [Flapjack.sptLookup_sptInsert_ne _ _ _ _ (by omega)]
      rfl
    rw [hnone]
    unfold mipsNameMap
    split <;> first | rfl | omega

end Flapjack.Compiler.Backend.Mips32Config
