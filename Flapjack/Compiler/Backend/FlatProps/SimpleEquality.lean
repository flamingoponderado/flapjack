module

public import Flapjack.Compiler.Backend.FlatProps.SimpleRelations
public import Flapjack.Compiler.Backend.Semantics.FlatSem.Operations
public import Mathlib.Data.List.Forall2

@[expose] public section

/-! Equality preservation for simple flat value relations. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.Compiler.Backend.FlatSem

/-- Equality groups both closure forms together and separates other values. -/
private def equalityShape : Value → Nat
  | .litv _ => 0
  | .loc _ _ => 1
  | .conv _ _ => 2
  | .vectorv _ => 3
  | .closure _ _ _ | .recclosure _ _ _ => 4

/-- Related values have the same equality class under a simple relation. -/
private theorem simpleRel_equalityShape (relation : Value → Value → Prop)
    (simple : simpleValueRel relation) (left right : Value) (related : relation left right) :
    equalityShape left = equalityShape right := by
  cases left with
  | litv lit =>
    have shape := ((simple.2 _ _ (by simp [isClosure])).1 related).1
    have eq : right = .litv lit := by simpa [simpleBasicValRel] using shape
    subst right; rfl
  | loc flag index =>
    have shape := ((simple.2 _ _ (by simp [isClosure])).1 related).1
    have eq : right = .loc flag index := by simpa [simpleBasicValRel] using shape
    subst right; rfl
  | conv stamp values =>
    have shape := ((simple.2 _ _ (by simp [isClosure])).1 related).1
    obtain ⟨values', rfl⟩ := shape
    rfl
  | vectorv values =>
    have shape := ((simple.2 _ _ (by simp [isClosure])).1 related).1
    obtain ⟨values', rfl⟩ := shape
    rfl
  | closure env name body =>
    have closure : isClosure right := (simple.1 _ _ related).1 (Or.inl ⟨env, name, body, rfl⟩)
    rcases closure with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
  | recclosure env functions name =>
    have closure : isClosure right := (simple.1 _ _ related).1 (Or.inr ⟨env, functions, name, rfl⟩)
    rcases closure with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl

/-- Different equality classes cause a flat equality type error. -/
private theorem doEq_differentShape (first second : Value) (different : equalityShape first ≠ equalityShape second) :
    doEq first second = .typeError := by
  cases first <;> cases second <;> simp_all [equalityShape, doEq]

/-- Values in the closure class compare equal. -/
private theorem doEq_closureShape (first second : Value)
    (firstShape : equalityShape first = 4) (secondShape : equalityShape second = 4) :
    doEq first second = .val true := by
  cases first <;> cases second <;> simp_all [equalityShape, doEq]

/-- List equality agrees when corresponding elements satisfy the induction hypothesis. -/
private theorem doEqList_congr {relation : Value → Value → Prop} {xs xs' ys ys' : List Value}
    (leftRel : List.Forall₂ relation xs xs') (rightRel : List.Forall₂ relation ys ys')
    (elementIH : ∀ x ∈ xs, ∀ y ∈ ys, ∀ x' y', relation x x' → relation y y' →
      doEq x y = doEq x' y') : doEqList xs ys = doEqList xs' ys' := by
  induction leftRel generalizing ys ys' with
  | nil => cases rightRel <;> simp [doEqList]
  | @cons x x' xs xs' xRel xsRel ih =>
    cases rightRel with
    | nil => simp [doEqList]
    | @cons y y' ys ys' yRel ysRel =>
      have head := elementIH x (by simp) y (by simp) x' y' xRel yRel
      have tail := ih ysRel (by
        intro a aMem b bMem a' b' ar br
        exact elementIH a (List.mem_cons_of_mem _ aMem) b (List.mem_cons_of_mem _ bMem) a' b' ar br)
      simp only [doEqList, ← head, tail]

/-- A simple value relation preserves the complete flat equality result.
This stronger fact supplies the successful-result theorem from HOL. -/
theorem doEq_simple (relation : Value → Value → Prop) (simple : simpleValueRel relation)
    (first second first' second' : Value) (firstRel : relation first first')
    (secondRel : relation second second') : doEq first second = doEq first' second' := by
  have firstShape := simpleRel_equalityShape relation simple first first' firstRel
  have secondShape := simpleRel_equalityShape relation simple second second' secondRel
  by_cases same : equalityShape first = equalityShape second
  · by_cases closure : equalityShape first = 4
    · have targetFirst : equalityShape first' = 4 := by omega
      have targetSecond : equalityShape second' = 4 := by omega
      rw [doEq_closureShape first second closure (by omega), doEq_closureShape first' second' targetFirst targetSecond]
    · cases first <;> cases second <;> simp only [equalityShape, Nat.reduceEqDiff, not_false_eq_true, not_true_eq_false] at same closure
      case litv.litv left right =>
        have leftShape := ((simple.2 _ _ (by simp [isClosure])).1 firstRel).1
        have rightShape := ((simple.2 _ _ (by simp [isClosure])).1 secondRel).1
        have leftEq : first' = .litv left := by simpa [simpleBasicValRel] using leftShape
        have rightEq : second' = .litv right := by simpa [simpleBasicValRel] using rightShape
        subst first'; subst second'; rfl
      case loc.loc leftFlag leftIndex rightFlag rightIndex =>
        have leftShape := ((simple.2 _ _ (by simp [isClosure])).1 firstRel).1
        have rightShape := ((simple.2 _ _ (by simp [isClosure])).1 secondRel).1
        have leftEq : first' = .loc leftFlag leftIndex := by simpa [simpleBasicValRel] using leftShape
        have rightEq : second' = .loc rightFlag rightIndex := by simpa [simpleBasicValRel] using rightShape
        subst first'; subst second'; rfl
      case conv.conv leftTag leftFields rightTag rightFields =>
        have leftInfo := (simple.2 _ _ (by simp [isClosure])).1 firstRel
        have rightInfo := (simple.2 _ _ (by simp [isClosure])).1 secondRel
        obtain ⟨leftFields', rfl⟩ := leftInfo.1
        obtain ⟨rightFields', rfl⟩ := rightInfo.1
        have leftRel : List.Forall₂ relation leftFields leftFields' := by simpa [valueContainerXs] using leftInfo.2
        have rightRel : List.Forall₂ relation rightFields rightFields' := by simpa [valueContainerXs] using rightInfo.2
        have leftLen := List.Forall₂.length_eq leftRel
        have rightLen := List.Forall₂.length_eq rightRel
        have lists := doEqList_congr leftRel rightRel (by
          intro x member y _ x' y' xRel yRel
          have small := List.sizeOf_lt_of_mem member
          have bound : sizeOf x < sizeOf (Value.conv leftTag leftFields) := by simp_wf; omega
          exact doEq_simple relation simple x y x' y' xRel yRel)
        simp [doEq, ← leftLen, ← rightLen, ← lists]
      case vectorv.vectorv leftFields rightFields =>
        have leftInfo := (simple.2 _ _ (by simp [isClosure])).1 firstRel
        have rightInfo := (simple.2 _ _ (by simp [isClosure])).1 secondRel
        obtain ⟨leftFields', rfl⟩ := leftInfo.1
        obtain ⟨rightFields', rfl⟩ := rightInfo.1
        have leftRel : List.Forall₂ relation leftFields leftFields' := by simpa [valueContainerXs] using leftInfo.2
        have rightRel : List.Forall₂ relation rightFields rightFields' := by simpa [valueContainerXs] using rightInfo.2
        have leftLen := List.Forall₂.length_eq leftRel
        have rightLen := List.Forall₂.length_eq rightRel
        have lists := doEqList_congr leftRel rightRel (by
          intro x member y _ x' y' xRel yRel
          have small := List.sizeOf_lt_of_mem member
          have bound : sizeOf x < sizeOf (Value.vectorv leftFields) := by simp_wf; omega
          exact doEq_simple relation simple x y x' y' xRel yRel)
        simp [doEq, ← leftLen, ← rightLen, ← lists]
  · have targetDifferent : equalityShape first' ≠ equalityShape second' := by omega
    rw [doEq_differentShape first second same, doEq_differentShape first' second' targetDifferent]
termination_by sizeOf first
decreasing_by all_goals subst_vars; all_goals assumption

/-- A simple relation preserves successful value and list equality results. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "simple_do_eq_thm_ind"]
theorem simpleDoEq_ind (relation : Value → Value → Prop) :
    (∀ x1 y1 x2 y2 b, simpleValueRel relation ∧ doEq x1 y1 = .val b ∧
      relation x1 x2 ∧ relation y1 y2 → doEq x2 y2 = .val b) ∧
    (∀ x1 y1 x2 y2 b, simpleValueRel relation ∧ doEqList x1 y1 = .val b ∧
      List.Forall₂ relation x1 x2 ∧ List.Forall₂ relation y1 y2 → doEqList x2 y2 = .val b) := by
  constructor
  · rintro x1 y1 x2 y2 b ⟨simple, run, xRel, yRel⟩
    exact (doEq_simple relation simple x1 y1 x2 y2 xRel yRel).symm.trans run
  · rintro x1 y1 x2 y2 b ⟨simple, run, xRel, yRel⟩
    have equal := doEqList_congr xRel yRel (by
      intro x _ y _ x' y' xRelated yRelated
      exact doEq_simple relation simple x y x' y' xRelated yRelated)
    exact equal.symm.trans run

/-- A simple relation preserves successful value equality results. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "simple_do_eq_thm"]
theorem simpleDoEq (relation : Value → Value → Prop) (x1 y1 x2 y2 : Value) (b : Bool)
    (premises : simpleValueRel relation ∧ doEq x1 y1 = .val b ∧
      relation x1 x2 ∧ relation y1 y2) : doEq x2 y2 = .val b :=
  (simpleDoEq_ind relation).1 x1 y1 x2 y2 b premises

end Flapjack.Compiler.Backend.FlatProps
