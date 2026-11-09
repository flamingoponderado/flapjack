module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Values.Stack

@[expose] public section

/-! Timestamp reachability through recursively nested data values. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- A timestamp in a traversed value comes from an enclosing list member.
This Flapjack helper follows the recursive value traversal. -/
theorem valueTimestamp_origin (values : List Value) :
    ∀ value ts, value ∈ valueListValues values → ts ∈ valueTimestamps value →
      ∃ root, root ∈ values ∧ ts ∈ valueTimestamps root := by
  induction values using valueListValues.induct with
  | case1 stamp tag children rest ihChildren ihRest =>
      intro value ts member timestamp
      simp only [valueListValues, List.mem_cons, List.mem_append] at member
      rcases member with (equal | nested) | tail
      · subst value
        exact ⟨.block stamp tag children, by simp, timestamp⟩
      · obtain ⟨root, inChildren, rootTimestamp⟩ := ihChildren value ts nested timestamp
        refine ⟨.block stamp tag children, by simp, ?_⟩
        simp only [valueTimestamps, List.mem_cons, List.mem_flatMap]
        exact Or.inr ⟨root, inChildren, rootTimestamp⟩
      · obtain ⟨root, inRest, rootTimestamp⟩ := ihRest value ts tail timestamp
        exact ⟨root, List.mem_cons_of_mem _ inRest, rootTimestamp⟩
  | case2 head rest notBlock ih =>
      intro value ts member timestamp
      have traversal : valueListValues (head :: rest) = head :: valueListValues rest := by
        cases head with
        | block stamp tag children => exact False.elim (notBlock stamp tag children rfl)
        | number _ => simp [valueListValues]
        | word64 _ => simp [valueListValues]
        | codePtr _ => simp [valueListValues]
        | refPtr _ _ => simp [valueListValues]
      rw [traversal, List.mem_cons] at member
      rcases member with equal | tail
      · subst value
        exact ⟨head, by simp, timestamp⟩
      · obtain ⟨root, inRest, rootTimestamp⟩ := ih value ts tail timestamp
        exact ⟨root, List.mem_cons_of_mem _ inRest, rootTimestamp⟩
  | case3 =>
      intro value ts member _
      simp [valueListValues] at member

/-- Timestamps of a nested value also occur in its enclosing value. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_all_vs_ts_MEM"]
theorem valueListValues_timestamp (value parent : Value) (ts : Nat)
    (h : ts ∈ valueTimestamps value ∧ value ∈ valueListValues [parent]) :
    ts ∈ valueTimestamps parent := by
  obtain ⟨root, member, timestamp⟩ := valueTimestamp_origin [parent] value ts h.2 h.1
  have same : root = parent := by simpa using member
  subst root
  exact timestamp

/-- A traversed block's timestamp occurs in its enclosing value. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_all_vs_ts"]
theorem blockTimestamp_of_nested (parent : Value) (ts tag : Nat) (values : List Value)
    (member : .block ts tag values ∈ valueListValues [parent]) : ts ∈ valueTimestamps parent := by
  apply valueListValues_timestamp (.block ts tag values) parent ts
  exact ⟨by simp [valueTimestamps], member⟩

/-- A nested block in a list traversal comes from one list member. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_all_vs_MEM2"]
theorem block_valueListValues_origin (values : List Value) (ts tag : Nat) (children : List Value)
    (member : .block ts tag children ∈ valueListValues values) :
    ∃ root, root ∈ values ∧ .block ts tag children ∈ valueListValues [root] :=
  valueListValues_member_origin values (.block ts tag children) member

/-- A timestamp found in a traversed value occurs in the flattened timestamps
of the original list. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_all_vs_ts_list"]
theorem valueListValues_timestamp_list (value : Value) (values : List Value) (ts : Nat)
    (h : value ∈ valueListValues values ∧ ts ∈ valueTimestamps value) :
    ts ∈ values.flatMap valueTimestamps := by
  obtain ⟨root, member, timestamp⟩ := valueTimestamp_origin values value ts h.1 h.2
  exact List.mem_flatMap.mpr ⟨root, member, timestamp⟩

/-- Timestamps of any recursively traversed value occur among the timestamps
of the stack or reference values. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "MEM_in_all_ts"]
theorem mem_allTimestamps (value : Value) (ts : Nat) (stack : List Value) (refs : Spt (BvlSem.Ref Value))
    (h : allValues refs stack value ∧ ts ∈ valueTimestamps value) : allTimestamps refs stack ts := by
  rcases h.1 with ⟨index, values, found, member⟩ |
    ⟨index, mode, child, found, member⟩ |
    ⟨index, tag, finalised, left, child, right, found, member⟩ | member
  · obtain ⟨root, inValues, timestamp⟩ := valueTimestamp_origin values value ts member h.2
    exact ⟨root, Or.inl ⟨index, .valueArray values, found, inValues⟩, timestamp⟩
  · obtain ⟨root, inValues, timestamp⟩ := valueTimestamp_origin [child] value ts member h.2
    have same : root = child := by simpa using inValues
    subst root
    exact ⟨child, Or.inl ⟨index, .thunk mode child, found, rfl⟩, timestamp⟩
  · obtain ⟨root, inValues, timestamp⟩ :=
      valueTimestamp_origin (left ++ [child] ++ right) value ts member h.2
    exact ⟨root, Or.inl ⟨index, .mutBlock tag finalised left child right, found, inValues⟩, timestamp⟩
  · obtain ⟨root, inStack, timestamp⟩ := valueTimestamp_origin stack value ts member h.2
    exact ⟨root, Or.inr inStack, timestamp⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
