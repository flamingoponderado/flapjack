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


/-- Actual ordered-map erasure has the original HOL filter's observations.
The input relation is sufficient; neither an output relation nor a target run
is assumed. All original store constructors and arbitrary duplicates remain. -/
theorem storeFacts_erase_transport {width : Nat} [NeZero width]
    (native : List (WordStoreHOL × Nat)) (executed : WordCseRegMap)
    (related : ∀ store, native.lookup store =
      executed[wordCseStoreCode (wordStoreFromHOL store : WordStore (BitVec width))]?)
    (store observed : WordStoreHOL) :
    (native.filter (fun entry => decide (entry.1 ≠ store))).lookup observed =
      (executed.erase (wordCseStoreCode (wordStoreFromHOL store : WordStore (BitVec width))))[wordCseStoreCode (wordStoreFromHOL observed : WordStore (BitVec width))]? := by
  rw [storeFacts_filter_lookup, Std.TreeMap.getElem?_erase]
  by_cases same : observed = store
  · subst observed; simp
  · have different :
        wordCseStoreCode (wordStoreFromHOL store : WordStore (BitVec width)) ≠
        wordCseStoreCode (wordStoreFromHOL observed : WordStore (BitVec width)) :=
      fun equal => same (storeCode_injective equal).symm
    simp only [same, if_false, Nat.compare_eq_eq, different]
    exact related observed

/-- Complete knowledge correspondence after the original store-fact removal.
The other four fields retain their input observations unchanged. -/
theorem knowledgeStoreErase_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed) (store : WordStoreHOL) :
    KnowledgeRel width
      { native with getsMem := native.getsMem.filter (fun entry => decide (entry.1 ≠ store)) }
      { executed with getsMem := (executed.getsMem.erase
          (wordCseStoreCode (wordStoreFromHOL store : WordStore (BitVec width)))) } := by
  refine ⟨related.1, related.2.1, ?_, related.2.2.2⟩
  intro observed
  exact storeFacts_erase_transport native.getsMem executed.getsMem related.2.2.1 store observed

/-- Complete knowledge correspondence after original association-list cons and
actual store insertion. Output observations are derived from the input relation. -/
theorem knowledgeStoreInsert_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed) (store : WordStoreHOL) (value : Nat) :
    KnowledgeRel width
      { native with getsMem := (store, value) :: native.getsMem }
      { executed with getsMem := (executed.getsMem.insert
          (wordCseStoreCode (wordStoreFromHOL store : WordStore (BitVec width))) value) } := by
  refine ⟨related.1, related.2.1, ?_, related.2.2.2⟩
  exact storeFacts_insert_transport native.getsMem executed.getsMem related.2.2.1 store value

end Flapjack.Compiler.Backend.WordCse
