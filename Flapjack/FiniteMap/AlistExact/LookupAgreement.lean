import Flapjack.FiniteMap.AlistExact.Lookup
import Batteries.Data.List.Basic

/-! Agreement between HOL association-list and Lean list lookup. -/
namespace Flapjack

/-- Propositional lookup agrees with the evaluator's list lookup whenever the
key's Boolean equality is lawful. -/
theorem holALookup_eq_lookup {K V : Type} [BEq K] [LawfulBEq K] (entries : List (K × V)) (key : K) :
    holALookup entries key = entries.lookup key := by
  classical
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨entryKey, value⟩ := entry
    by_cases same : key = entryKey
    · subst entryKey
      simp [holALookup]
    · have beqFalse : (key == entryKey) = false := by
        cases h : key == entryKey <;> simp_all [beq_iff_eq]
      simp [holALookup, List.lookup_cons, same, beqFalse, ih]

/-- Shared infrastructure for the two compiler proofs' key-preserving lookup lemmas. -/
theorem holALookup_map_keyPreserving {K A B : Type} (xs : List (K × A))
    (f : K × A → K × B) (key : K) (keys : ∀ x ∈ xs, (f x).1 = x.1) :
    holALookup (xs.map f) key = (holALookup xs key).map (fun value => (f (key, value)).2) := by
  classical
  induction xs with
  | nil => simp [holALookup]
  | cons pair rest ih =>
    have first := keys pair (by simp)
    have tail : ∀ x ∈ rest, (f x).1 = x.1 := by
      intro x member
      exact keys x (List.mem_cons_of_mem _ member)
    obtain ⟨headKey, headValue⟩ := pair
    cases result : f (headKey, headValue) with
    | mk mappedKey mappedValue =>
      have same : mappedKey = headKey := by simpa [result] using first
      subst mappedKey
      by_cases eq : key = headKey
      · subst key
        simp [holALookup, result]
      · simp [holALookup, result, eq, ih tail]

end Flapjack
