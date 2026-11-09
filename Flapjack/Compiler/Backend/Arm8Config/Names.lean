module

public import Flapjack.Misc.Sptree
public import Flapjack.HolRef
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace Flapjack.Compiler.Backend.Arm8Config

/-- CakeML's ARMv8 register names: stack-language register `k` is machine register
`arm8NameLookup k`.  Source 0 is the link register `x30`, source 1-4 are the argument
registers `x0`-`x3`, target `x18` (platform reserved), `x26` (encoder temporary) and
`x31` (stack pointer) are avoided, and the top three source registers 26-28 are
callee-saved in `x19`-`x28`. -/
@[hol "cakeml/compiler/backend/arm8/arm8_configScript.sml" "arm8_names_def" 10]
def arm8Names : Flapjack.Spt Nat :=
  Flapjack.sptInsert 0 30 (Flapjack.sptInsert 1 0 (Flapjack.sptInsert 2 1
    (Flapjack.sptInsert 3 2 (Flapjack.sptInsert 4 3 (Flapjack.sptInsert 18 4
    (Flapjack.sptInsert 25 29 (Flapjack.sptInsert 26 25 (Flapjack.sptInsert 29 18
    (Flapjack.sptInsert 30 26 .ln)))))))))

/-- Identity-default lookup in `arm8Names` (Flapjack infrastructure). -/
def arm8NameLookup (register : Nat) : Nat :=
  (Flapjack.sptLookup register arm8Names).getD register

/-- `arm8Names` as an explicit function (Flapjack infrastructure for deciding facts about
the names). -/
def arm8NameMap (register : Nat) : Nat :=
  match register with
  | 0 => 30 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 18 => 4 | 25 => 29 | 26 => 25
  | 29 => 18 | 30 => 26 | r => r

theorem arm8Names_lookup_eq (register : Nat) :
    (Flapjack.sptLookup register arm8Names).getD register = arm8NameMap register := by
  by_cases h : register < 32
  · interval_cases register <;>
      simp [arm8Names, Flapjack.sptInsert, Flapjack.sptLookup, arm8NameMap]
  · have hnone : Flapjack.sptLookup register arm8Names = none := by
      unfold arm8Names
      repeat rw [Flapjack.sptLookup_sptInsert_ne _ _ _ _ (by omega)]
      rfl
    rw [hnone]
    unfold arm8NameMap
    split <;> first | rfl | omega

/-- The inverse of `arm8NameMap` (Flapjack infrastructure): the ten-cycle
`0 → 30 → 26 → 25 → 29 → 18 → 4 → 3 → 2 → 1 → 0` reversed, identity elsewhere. -/
def arm8NameInv (register : Nat) : Nat :=
  match register with
  | 30 => 0 | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 18 | 29 => 25
  | 25 => 26 | 18 => 29 | 26 => 30 | r => r

/-- `arm8NameInv` is a left inverse of `arm8NameMap`: the names map is injective. -/
theorem arm8NameInv_map (k : Nat) : arm8NameInv (arm8NameMap k) = k := by
  by_cases h : k < 32
  · interval_cases k <;> rfl
  · unfold arm8NameMap
    split <;> (try omega)
    unfold arm8NameInv
    split <;> first | rfl | omega

/-- `arm8NameInv` is a right inverse of `arm8NameMap`: the names map is surjective. -/
theorem arm8NameMap_inv (k : Nat) : arm8NameMap (arm8NameInv k) = k := by
  by_cases h : k < 32
  · interval_cases k <;> rfl
  · unfold arm8NameInv
    split <;> (try omega)
    unfold arm8NameMap
    split <;> first | rfl | omega

end Flapjack.Compiler.Backend.Arm8Config
