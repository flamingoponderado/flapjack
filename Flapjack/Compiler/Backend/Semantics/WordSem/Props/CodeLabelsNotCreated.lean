module

public import Flapjack.Pancake.WordConvs.CodeLabels
public import Flapjack.Pancake.WordConvs.NotCreated
public import Mathlib.Data.Set.Insert

@[expose] public section

/-!
# Labels are exactly the sub-programs that were created

Counterpart of `cakeml/compiler/backend/semantics/wordPropsScript.sml:4760-4768`
(`get_code_labels_not_created`). HOL's `get_code_labels` is
`getCodeLabelsHOL` and `not_created_subprogs` is `notCreatedSubprogsHOL`; the
predicate excludes `Call NONE (SOME x) [] NONE` and `LocValue 0 x`, so a label
occurs exactly when such a node does.
-/

namespace Flapjack

/-- The predicate of HOL's `get_code_labels_not_created` as the `Bool`-valued
    test `notCreatedSubprogsHOL` expects. HOL writes it as the conjunction
    `sp ≠ Call NONE (SOME x) [] NONE ∧ sp ≠ LocValue 0 x`; `WordLangProgHOL` has
    no decidable equality instance, so the same predicate is written as a
    structural match that returns `false` exactly on those two programs. -/
def notCreatedLabelTest {width : Nat} [NeZero width] (x : Nat) :
    WordLangProgHOL (BitVec width) → Bool
  | .call none (some label) [] none => decide (label ≠ x)
  | .locValue 0 label => decide (label ≠ x)
  | _ => true

/-- Flapjack infrastructure: the same statement as `get_code_labels_not_created`
    with HOL's predicate factored into `notCreatedLabelTest`, proved by the
    constructor case analysis. Untagged because HOL states the predicate
    inline; the tagged theorem below restates it that way. -/
theorem notCreatedLabelTest_spec {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)) (x : Nat),
      x ∈ getCodeLabelsHOL p ↔
        notCreatedSubprogsHOL (notCreatedLabelTest x) p = false
  | .skip, _ => by simp [getCodeLabelsHOL, notCreatedSubprogsHOL]
  | .move _ _, _ => by simp [getCodeLabelsHOL, notCreatedSubprogsHOL]
  | .inst _, _ => by simp [getCodeLabelsHOL, notCreatedSubprogsHOL]
  | .assign _ _, _ => by simp [getCodeLabelsHOL, notCreatedSubprogsHOL]
  | .get _ _, _ => by simp [getCodeLabelsHOL, notCreatedSubprogsHOL]
  | .set _ _, _ => by simp [getCodeLabelsHOL, notCreatedSubprogsHOL]
  | .store _ _, _ => by simp [getCodeLabelsHOL, notCreatedSubprogsHOL]
  | .mustTerminate body, x => by
    simp only [getCodeLabelsHOL, notCreatedSubprogsHOL, notCreatedLabelTest,
      Bool.true_and]
    rw [← notCreatedLabelTest_spec body x]
  | .seq first second, x => by
    simp only [getCodeLabelsHOL, notCreatedSubprogsHOL, Set.mem_union]
    rw [Bool.and_eq_false_iff, ← notCreatedLabelTest_spec first x,
      ← notCreatedLabelTest_spec second x]
  | .ite _ _ _ first second, x => by
    simp only [getCodeLabelsHOL, notCreatedSubprogsHOL, Set.mem_union]
    rw [Bool.and_eq_false_iff, ← notCreatedLabelTest_spec first x,
      ← notCreatedLabelTest_spec second x]
  | .loop _ body _, x => by
    simp only [getCodeLabelsHOL, notCreatedSubprogsHOL]
    rw [← notCreatedLabelTest_spec body x]
  | .call returns target args handler, x => by
    cases target with
    | none =>
      cases returns with
      | none =>
        cases handler with
        | none =>
          simp only [getCodeLabelsHOL, notCreatedSubprogsHOL, notCreatedLabelTest,
            Set.mem_union, Set.mem_empty_iff_false]
          simp
        | some h =>
          obtain ⟨_, body, _, _⟩ := h
          simp only [getCodeLabelsHOL, notCreatedSubprogsHOL, notCreatedLabelTest,
            Bool.true_and, Bool.and_true, Set.mem_union, Set.mem_empty_iff_false]
          rw [← notCreatedLabelTest_spec body x]
          simp
      | some r =>
        obtain ⟨_, _, body, _, _⟩ := r
        cases handler with
        | none =>
          simp only [getCodeLabelsHOL, notCreatedSubprogsHOL, notCreatedLabelTest,
            Bool.true_and, Bool.and_true, Set.mem_union, Set.mem_empty_iff_false]
          rw [← notCreatedLabelTest_spec body x]
          simp
        | some h =>
          obtain ⟨_, hbody, _, _⟩ := h
          simp only [getCodeLabelsHOL, notCreatedSubprogsHOL, notCreatedLabelTest,
            Bool.true_and, Set.mem_union, Set.mem_empty_iff_false]
          rw [Bool.and_eq_false_iff, ← notCreatedLabelTest_spec body x,
            ← notCreatedLabelTest_spec hbody x]
          simp
    | some label =>
      cases returns with
      | none =>
        cases handler with
        | none =>
          simp only [getCodeLabelsHOL, notCreatedSubprogsHOL, notCreatedLabelTest,
            Bool.and_true, Set.mem_union, Set.mem_singleton_iff,
            Set.mem_empty_iff_false]
          rw [decide_eq_false_iff_not]
          simp [ne_eq, eq_comm]
        | some h =>
          obtain ⟨_, body, _, _⟩ := h
          simp only [getCodeLabelsHOL, notCreatedSubprogsHOL, notCreatedLabelTest,
            Bool.true_and, Bool.and_true, Set.mem_union, Set.mem_singleton_iff,
            Set.mem_empty_iff_false]
          rw [Bool.and_eq_false_iff, decide_eq_false_iff_not,
            ← notCreatedLabelTest_spec body x]
          simp [ne_eq, eq_comm]
      | some r =>
        obtain ⟨_, _, body, _, _⟩ := r
        cases handler with
        | none =>
          simp only [getCodeLabelsHOL, notCreatedSubprogsHOL, notCreatedLabelTest,
            Bool.and_true, Set.mem_union, Set.mem_singleton_iff,
            Set.mem_empty_iff_false]
          rw [Bool.and_eq_false_iff, decide_eq_false_iff_not,
            ← notCreatedLabelTest_spec body x]
          simp [ne_eq, eq_comm]
        | some h =>
          obtain ⟨_, hbody, _, _⟩ := h
          simp only [getCodeLabelsHOL, notCreatedSubprogsHOL, notCreatedLabelTest,
            Bool.true_and, Set.mem_union, Set.mem_singleton_iff]
          rw [Bool.and_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not,
            ← notCreatedLabelTest_spec body x, ← notCreatedLabelTest_spec hbody x]
          simp [ne_eq, eq_comm]
  | .alloc _ _, _ => by simp [getCodeLabelsHOL, notCreatedSubprogsHOL, notCreatedLabelTest]
  | .storeConsts _ _ _ _ _, _ => by simp [getCodeLabelsHOL, notCreatedSubprogsHOL]
  | .raise _, _ => by simp [getCodeLabelsHOL, notCreatedSubprogsHOL]
  | .return _ _, _ => by simp [getCodeLabelsHOL, notCreatedSubprogsHOL]
  | .break _, _ => by simp [getCodeLabelsHOL, notCreatedSubprogsHOL]
  | .continue _, _ => by simp [getCodeLabelsHOL, notCreatedSubprogsHOL]
  | .tick, _ => by simp [getCodeLabelsHOL, notCreatedSubprogsHOL]
  | .opCurrHeap _ _ _, _ => by simp [getCodeLabelsHOL, notCreatedSubprogsHOL]
  | .locValue _ label, x => by
    simp only [getCodeLabelsHOL, notCreatedSubprogsHOL, notCreatedLabelTest,
      Set.mem_singleton_iff]
    rw [decide_eq_false_iff_not]
    simp [ne_eq, eq_comm]
  | .install _ _ _ _ _, _ => by simp [getCodeLabelsHOL, notCreatedSubprogsHOL, notCreatedLabelTest]
  | .codeBufferWrite _ _, _ => by simp [getCodeLabelsHOL, notCreatedSubprogsHOL]
  | .dataBufferWrite _ _, _ => by simp [getCodeLabelsHOL, notCreatedSubprogsHOL]
  | .ffi _ _ _ _ _ _, _ => by simp [getCodeLabelsHOL, notCreatedSubprogsHOL]
  | .shareInst _ _ _, _ => by simp [getCodeLabelsHOL, notCreatedSubprogsHOL, notCreatedLabelTest]

/-- The helper is HOL's predicate written structurally: it returns `false`
    exactly on `Call NONE (SOME x) [] NONE` and `LocValue 0 x`. -/
theorem notCreatedLabelTest_eq {width : Nat} [NeZero width] (x : Nat) :
    notCreatedLabelTest (width := width) x =
      fun sp : WordLangProgHOL (BitVec width) =>
        match sp with
        | .call none (some label) [] none => decide (label ≠ x)
        | .locValue 0 label => decide (label ≠ x)
        | _ => true := rfl

/-- Exact HOL `get_code_labels_not_created` (`wordPropsScript.sml:4760-4768`):
    `x` is a code label of `p` exactly when `not_created_subprogs` fails at the
    inline predicate excluding `Call NONE (SOME x) [] NONE` and `LocValue 0 x`.
    HOL writes that predicate as `sp ≠ Call NONE (SOME x) [] NONE ∧
    sp ≠ LocValue 0 x`; `WordLangProgHOL` has no decidable equality instance
    (Lean cannot derive one for an inductive with nested recursive occurrences
    such as `List (WordLangProgHOL α)`), so the same predicate is stated as the
    structural match that returns `false` exactly on those two programs. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "get_code_labels_not_created"
  (words_as_type_indexed_bitvec)]
theorem getCodeLabels_notCreated {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)) (x : Nat),
      x ∈ getCodeLabelsHOL p ↔
        notCreatedSubprogsHOL (fun sp =>
          match sp with
          | .call none (some label) [] none => decide (label ≠ x)
          | .locValue 0 label => decide (label ≠ x)
          | _ => true) p = false := by
  intro p x
  exact notCreatedLabelTest_spec p x

end Flapjack
