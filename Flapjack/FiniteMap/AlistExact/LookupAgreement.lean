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

end Flapjack
