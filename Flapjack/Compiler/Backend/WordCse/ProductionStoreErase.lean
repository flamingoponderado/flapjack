import Flapjack.Compiler.Backend.WordCse.ProductionStoreFacts

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack RiscV

/-- The original Set filter removes every matching store fact, including
shadowed duplicates; it preserves the first lookup of every other store.
Flapjack representation infrastructure for the actual store carrier. -/
theorem storeFacts_filter_lookup (native : List (WordStoreHOL × Nat))
    (store observed : WordStoreHOL) :
    (native.filter (fun entry => decide (entry.1 ≠ store))).lookup observed =
      if observed = store then none else native.lookup observed := by
  induction native with
  | nil => simp [List.lookup]
  | cons pair tail ih =>
    rcases pair with ⟨key, value⟩
    simp only [List.filter_cons]
    by_cases removed : key = store
    · have predicate : decide (key ≠ store) = false := by simp [removed]
      rw [predicate]
      simp only [Bool.false_eq_true, if_false]
      subst key
      by_cases same : observed = store
      · rw [if_pos same] at ih ⊢
        exact ih
      · rw [if_neg same] at ih ⊢
        simpa only [List.lookup, Bool.beq_eq_decide_eq, same, decide_false] using ih
    · have predicate : decide (key ≠ store) = true := by simp [removed]
      rw [predicate]
      simp only [if_true, List.lookup, Bool.beq_eq_decide_eq]
      by_cases head : observed = key
      · simp [head, removed]
      · simp only [head, decide_false]
        exact ih

end Flapjack.Compiler.Backend.WordCse
