import Flapjack.Misc.BalancedMap.Insert
import Flapjack.Misc.BalancedMap.InvariantSemantics
import Flapjack.Misc.BalancedMap.KeySets
import Flapjack.FiniteMap.MapKeys
namespace Flapjack.Misc.BalancedMap
open FiniteMap.Comparison
/-- Comparator-equivalence transport infrastructure; no separate HOL original. -/
private theorem orderedEqualTransport {κ ν : Type} (cmp : κ → κ → Ordering)
    (hgood : goodCmp cmp) (key root : κ) (heq : cmp key root = .eq)
    (tree : Map κ ν) (result : Ordering) :
    keyOrdered cmp root tree result → keyOrdered cmp key tree result := by
  induction tree with
  | tip => exact fun _ => trivial
  | bin n x value left right ihleft ihright =>
    rintro ⟨hroot, hl, hr⟩
    refine ⟨?_, ihleft hl, ihright hr⟩
    rcases hgood with ⟨_, hsym, hswap, heqLt, hltEq, heqEq, _⟩
    cases result with
    | lt => exact heqLt key root x ⟨heq, hroot⟩
    | eq => exact heqEq key root x ⟨heq, hroot⟩
    | gt =>
        exact (hswap key x).mpr (hltEq x root key ⟨(hswap root x).mp hroot, hsym key root heq⟩)

/-- Equal constructor branch of full insertion correctness. Untagged during
implementation until the complete case statement/source comparison is reviewed. -/
theorem insertCorrectEqual {κ ν : Type} (cmp : κ → κ → Ordering)
    (key root : κ) (value oldValue : ν) (n : Nat) (left right : Map κ ν)
    (hgood : goodCmp cmp) (hinv : invariant cmp (.bin n root oldValue left right))
    (heq : cmp key root = .eq) :
    invariant cmp (insert cmp key value (.bin n root oldValue left right)) ∧
      toFmap cmp (insert cmp key value (.bin n root oldValue left right)) =
        (toFmap cmp (.bin n root oldValue left right)).updateEq (keySet cmp key, value) := by
  classical
  rw [insert, heq]
  rcases hinv with ⟨hs, hl, hr, hb, hil, hir⟩
  refine ⟨⟨hs, orderedEqualTransport cmp hgood key root heq left .gt hl,
    orderedEqualTransport cmp hgood key root heq right .lt hr, hb, hil, hir⟩, ?_⟩
  have hk : keySet cmp key = keySet cmp root := (keySetEq cmp key root hgood).mpr heq
  apply HolFiniteMapExact.ext_lookup
  intro query
  simp only [toFmap, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hk]
  split_ifs <;> rfl
end Flapjack.Misc.BalancedMap
