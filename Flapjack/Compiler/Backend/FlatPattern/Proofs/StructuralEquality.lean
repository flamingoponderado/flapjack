import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveComparison

/-! Structural equality for the proof-side flat pattern relations. The flat
evaluator and relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend

/-- Pairwise related lists compare identically when the equality induction
hypothesis holds for their elements. This includes unequal lengths and all
short-circuit outcomes. -/
theorem doEqList_related {xs xs' ys ys' : List FlatSem.Value}
    (leftRel : List.Forall₂ ValueRel xs xs') (rightRel : List.Forall₂ ValueRel ys ys')
    (elementIH : ∀ x ∈ xs, ∀ y ∈ ys, ∀ x' y', ValueRel x x' → ValueRel y y' →
      FlatSem.doEq x y = FlatSem.doEq x' y') :
    FlatSem.doEqList xs ys = FlatSem.doEqList xs' ys' := by
  induction leftRel generalizing ys ys' with
  | nil =>
    cases rightRel <;> simp [FlatSem.doEqList]
  | @cons x x' xs xs' xRel xsRel ih =>
    cases rightRel with
    | nil => simp [FlatSem.doEqList]
    | @cons y y' ys ys' yRel ysRel =>
      have head := elementIH x (by simp) y (by simp) x' y' xRel yRel
      have tail := ih ysRel (by
        intro a aMem b bMem a' b' ar br
        exact elementIH a (List.mem_cons_of_mem _ aMem) b (List.mem_cons_of_mem _ bMem) a' b' ar br)
      simp only [FlatSem.doEqList, ← head, tail]

/-- Equality of related constructor values follows from the element induction
hypothesis and preserves tag and length checks. -/
theorem doEq_constructor_step (leftTag rightTag : Option (FlatLang.CtorId × FlatLang.TypeId))
    (xs xs' ys ys' : List FlatSem.Value) (leftRel : List.Forall₂ ValueRel xs xs')
    (rightRel : List.Forall₂ ValueRel ys ys')
    (elementIH : ∀ x ∈ xs, ∀ y ∈ ys, ∀ x' y', ValueRel x x' → ValueRel y y' →
      FlatSem.doEq x y = FlatSem.doEq x' y') :
    FlatSem.doEq (.conv leftTag xs) (.conv rightTag ys) = FlatSem.doEq (.conv leftTag xs') (.conv rightTag ys') := by
  have leftLen := forall₂_length leftRel
  have rightLen := forall₂_length rightRel
  have lists := doEqList_related leftRel rightRel elementIH
  simp [FlatSem.doEq, ← leftLen, ← rightLen, ← lists]

/-- Equality of related vectors follows from the element induction hypothesis. -/
theorem doEq_vector_step (xs xs' ys ys' : List FlatSem.Value) (leftRel : List.Forall₂ ValueRel xs xs')
    (rightRel : List.Forall₂ ValueRel ys ys')
    (elementIH : ∀ x ∈ xs, ∀ y ∈ ys, ∀ x' y', ValueRel x x' → ValueRel y y' →
      FlatSem.doEq x y = FlatSem.doEq x' y') :
    FlatSem.doEq (.vectorv xs) (.vectorv ys) = FlatSem.doEq (.vectorv xs') (.vectorv ys') := by
  have leftLen := forall₂_length leftRel
  have rightLen := forall₂_length rightRel
  have lists := doEqList_related leftRel rightRel elementIH
  simp [FlatSem.doEq, ← leftLen, ← rightLen, ← lists]

/-- Equality distinguishes these value classes; both kinds of closure share
the same class because the evaluator compares them as closures. -/
def equalityShape : FlatSem.Value → Nat
  | .litv _ => 0
  | .loc _ _ => 1
  | .conv _ _ => 2
  | .vectorv _ => 3
  | .closure _ _ _ | .recclosure _ _ _ => 4

/-- Related values have the same equality class. -/
theorem valueRel_equalityShape (value value' : FlatSem.Value) (related : ValueRel value value') :
    equalityShape value = equalityShape value' := by
  cases value with
  | litv lit => have eq := (valueRel_lit lit value').1 related; subst value'; rfl
  | loc flag index => have eq := (valueRel_loc flag index value').1 related; subst value'; rfl
  | conv tag fields => obtain ⟨_, rfl, _⟩ := (valueRel_conv tag fields value').1 related; rfl
  | vectorv fields => obtain ⟨_, rfl, _⟩ := (valueRel_vector fields value').1 related; rfl
  | closure env name body => obtain ⟨_, _, _, _, _, rfl⟩ := (valueRel_closure env name body value').1 related; rfl
  | recclosure env funs name => obtain ⟨_, _, _, _, _, rfl⟩ := (valueRel_recclosure env funs name value').1 related; rfl

/-- Different equality classes always produce a type error. -/
theorem doEq_differentShape (first second : FlatSem.Value) (different : equalityShape first ≠ equalityShape second) :
    FlatSem.doEq first second = .typeError := by
  cases first <;> cases second <;> simp_all [equalityShape, FlatSem.doEq]

/-- Two closure-class values compare equal in the flat evaluator. -/
theorem doEq_closureShape (first second : FlatSem.Value)
    (firstShape : equalityShape first = 4) (secondShape : equalityShape second = 4) :
    FlatSem.doEq first second = .val true := by
  cases first <;> cases second <;> simp_all [equalityShape, FlatSem.doEq]

/-- Structural equality returns the same result for related values. -/
theorem doEq_related (first second first' second' : FlatSem.Value)
    (firstRel : ValueRel first first') (secondRel : ValueRel second second') :
    FlatSem.doEq first second = FlatSem.doEq first' second' := by
  have firstShape := valueRel_equalityShape first first' firstRel
  have secondShape := valueRel_equalityShape second second' secondRel
  by_cases same : equalityShape first = equalityShape second
  · by_cases closure : equalityShape first = 4
    · have targetFirst : equalityShape first' = 4 := by omega
      have targetSecond : equalityShape second' = 4 := by omega
      rw [doEq_closureShape first second closure (by omega), doEq_closureShape first' second' targetFirst targetSecond]
    · cases first <;> cases second <;> simp only [equalityShape, Nat.reduceEqDiff, not_false_eq_true, not_true_eq_false] at same closure
      case litv.litv left right =>
        have leftEq := (valueRel_lit left first').1 firstRel
        have rightEq := (valueRel_lit right second').1 secondRel
        subst first'
        subst second'
        rfl
      case loc.loc leftFlag leftIndex rightFlag rightIndex =>
        have leftEq := (valueRel_loc leftFlag leftIndex first').1 firstRel
        have rightEq := (valueRel_loc rightFlag rightIndex second').1 secondRel
        subst first'
        subst second'
        rfl
      case conv.conv leftTag leftFields rightTag rightFields =>
        obtain ⟨leftFields', rfl, leftRel⟩ := (valueRel_conv leftTag leftFields first').1 firstRel
        obtain ⟨rightFields', rfl, rightRel⟩ := (valueRel_conv rightTag rightFields second').1 secondRel
        apply doEq_constructor_step leftTag rightTag leftFields leftFields' rightFields rightFields' leftRel rightRel
        intro x member y _ x' y' xRel yRel
        have small := List.sizeOf_lt_of_mem member
        have bound : sizeOf x < sizeOf (FlatSem.Value.conv leftTag leftFields) := by simp_wf; omega
        exact doEq_related x y x' y' xRel yRel
      case vectorv.vectorv leftFields rightFields =>
        obtain ⟨leftFields', rfl, leftRel⟩ := (valueRel_vector leftFields first').1 firstRel
        obtain ⟨rightFields', rfl, rightRel⟩ := (valueRel_vector rightFields second').1 secondRel
        apply doEq_vector_step leftFields leftFields' rightFields rightFields' leftRel rightRel
        intro x member y _ x' y' xRel yRel
        have small := List.sizeOf_lt_of_mem member
        have bound : sizeOf x < sizeOf (FlatSem.Value.vectorv leftFields) := by simp_wf; omega
        exact doEq_related x y x' y' xRel yRel
  · have targetDifferent : equalityShape first' ≠ equalityShape second' := by omega
    rw [doEq_differentShape first second same, doEq_differentShape first' second' targetDifferent]
termination_by sizeOf first
decreasing_by all_goals simp_wf; all_goals subst_vars; all_goals assumption

/-- General equality preserves successful primitive results for related values. -/
theorem doApp_equality_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (values values' : List FlatSem.Value) (result : SemanticPrimitivesHOL.Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src .equality) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src .equality) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases related with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric] at run
  | @cons first first' tail tail' firstRel rest =>
    cases rest with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric] at run
    | @cons second second' tail tail' secondRel rest =>
      cases rest with
      | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppNumeric] at run
      | nil =>
        have equality := doEq_related first second first' second' firstRel secondRel
        cases compared : FlatSem.doEq first second with
        | typeError => simp [FlatSem.doApp, FlatSem.doAppNumeric, compared] at run
        | val boolean =>
          have compared' : FlatSem.doEq first' second' = .val boolean := by rw [← equality, compared]
          simp [FlatSem.doApp, FlatSem.doAppNumeric, compared] at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨target, .val (FlatSem.boolValue boolean), by simp [FlatSem.doApp, FlatSem.doAppNumeric, compared'],
            states, .value (boolValue_related boolean)⟩

end Flapjack.Compiler.Backend.FlatPattern
