module

public import Flapjack.Misc.Sptree

@[expose] public section

namespace Flapjack

/-- Flapjack infrastructure for HOL approximation invariants: inserting a
value satisfying a predicate preserves the predicate for every stored value. -/
theorem sptInsert_preservesProperty {A : Type} (P : A → Prop) (g : Spt A) (index : Nat) (a : A)
    (safe : P a) (globals : ∀ n v, sptLookup n g = some v → P v) :
    ∀ n v, sptLookup n (sptInsert index a g) = some v → P v := by
  intro key value lookup
  by_cases same : key = index
  · subst key
    rw [sptLookup_sptInsert_same] at lookup
    cases lookup
    exact safe
  · rw [sptLookup_sptInsert_ne index key a g same] at lookup
    exact globals key value lookup

end Flapjack
