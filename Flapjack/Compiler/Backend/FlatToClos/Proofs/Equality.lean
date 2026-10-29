import Flapjack.Compiler.Backend.FlatToClos.Proofs.ValueRelation
import Flapjack.Compiler.Backend.Semantics.FlatSem.Operations

/-! Proof-side facts for polymorphic equality during flat-to-closure lowering. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL

/-- List equality preserves a successful result if equality of related
individual values does. This is an induction helper, not a HOL port. -/
theorem doEqList_related_of_values
    (step : ∀ s₁ t₁ s₂ t₂ b, ValueRel s₁ t₁ → ValueRel s₂ t₂ →
      FlatSem.doEq s₁ s₂ = .val b → ClosSem.doEq t₁ t₂ = .val b)
    {s₁ s₂ : List FlatSem.Value} {t₁ t₂ : List ClosSem.Value} (first : List.Forall₂ ValueRel s₁ t₁)
    (second : List.Forall₂ ValueRel s₂ t₂) (b : Bool)
    (result : FlatSem.doEqList s₁ s₂ = .val b) :
    ClosSem.doEqList t₁ t₂ = .val b := by
  induction first generalizing s₂ t₂ b with
  | nil =>
    cases second <;> simpa [FlatSem.doEqList, ClosSem.doEqList] using result
  | @cons sourceHead targetHead _ _ head tail ih =>
    cases second with
    | nil => simpa [FlatSem.doEqList, ClosSem.doEqList] using result
    | cons head₂ tail₂ =>
      rename_i sourceHead₂ targetHead₂ _ _
      cases h : FlatSem.doEq sourceHead sourceHead₂ with
      | typeError => simp [FlatSem.doEqList, h] at result
      | val value =>
        have targetEq := step _ _ _ _ value head head₂ h
        cases value with
        | false => simpa [FlatSem.doEqList, ClosSem.doEqList, h, targetEq] using result
        | true =>
          simp only [FlatSem.doEqList, h] at result
          simpa [ClosSem.doEqList, targetEq] using ih tail₂ b result

private theorem related_length {source : List FlatSem.Value} {target : List ClosSem.Value}
    (related : List.Forall₂ ValueRel source target) : source.length = target.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Successful vector comparison is preserved when the related elements'
comparisons are preserved. -/
theorem doEq_vector_related_of_values
    (step : ∀ s₁ t₁ s₂ t₂ b, ValueRel s₁ t₁ → ValueRel s₂ t₂ →
      FlatSem.doEq s₁ s₂ = .val b → ClosSem.doEq t₁ t₂ = .val b)
    {s₁ s₂ : List FlatSem.Value} {t₁ t₂ : List ClosSem.Value}
    (first : List.Forall₂ ValueRel s₁ t₁) (second : List.Forall₂ ValueRel s₂ t₂)
    (b : Bool) (result : FlatSem.doEq (.vectorv s₁) (.vectorv s₂) = .val b) :
    ClosSem.doEq (.block 0 t₁) (.block 0 t₂) = .val b := by
  have lengths : (s₁.length = s₂.length) ↔ (t₁.length = t₂.length) := by
    rw [← related_length first, ← related_length second]
  by_cases same : s₁.length = s₂.length
  · have related := doEqList_related_of_values step first second b (by simpa [FlatSem.doEq, same] using result)
    simpa [ClosSem.doEq, lengths.mp same] using related
  · have targetDifferent : t₁.length ≠ t₂.length := fun h => same (lengths.mpr h)
    simpa [FlatSem.doEq, ClosSem.doEq, same, targetDifferent] using result

/-- Successful tuple comparison is preserved when the related elements'
comparisons are preserved. -/
theorem doEq_tuple_related_of_values
    (step : ∀ s₁ t₁ s₂ t₂ b, ValueRel s₁ t₁ → ValueRel s₂ t₂ →
      FlatSem.doEq s₁ s₂ = .val b → ClosSem.doEq t₁ t₂ = .val b)
    {s₁ s₂ : List FlatSem.Value} {t₁ t₂ : List ClosSem.Value}
    (first : List.Forall₂ ValueRel s₁ t₁) (second : List.Forall₂ ValueRel s₂ t₂)
    (b : Bool) (result : FlatSem.doEq (.conv none s₁) (.conv none s₂) = .val b) :
    ClosSem.doEq (.block 0 t₁) (.block 0 t₂) = .val b := by
  have lengths : (s₁.length = s₂.length) ↔ (t₁.length = t₂.length) := by
    rw [← related_length first, ← related_length second]
  by_cases same : s₁.length = s₂.length
  · have related := doEqList_related_of_values step first second b (by simpa [FlatSem.doEq, same] using result)
    simpa [ClosSem.doEq, lengths.mp same] using related
  · have targetDifferent : t₁.length ≠ t₂.length := fun h => same (lengths.mpr h)
    simpa [FlatSem.doEq, FlatSem.ctorSameType, ClosSem.doEq, same, targetDifferent] using result

/-- Successful tagged-constructor comparison is preserved when the related
fields' comparisons are preserved. A source type error is not assumed to
have a corresponding target result. -/
theorem doEq_con_related_of_values
    (step : ∀ s₁ t₁ s₂ t₂ b, ValueRel s₁ t₁ → ValueRel s₂ t₂ →
      FlatSem.doEq s₁ s₂ = .val b → ClosSem.doEq t₁ t₂ = .val b)
    {s₁ s₂ : List FlatSem.Value} {t₁ t₂ : List ClosSem.Value}
    (first : List.Forall₂ ValueRel s₁ t₁) (second : List.Forall₂ ValueRel s₂ t₂)
    (tag₁ tag₂ : FlatLang.CtorId) (type₁ type₂ : FlatLang.TypeId) (b : Bool)
    (result : FlatSem.doEq (.conv (some (tag₁, type₁)) s₁)
      (.conv (some (tag₂, type₂)) s₂) = .val b) :
    ClosSem.doEq (.block tag₁ t₁) (.block tag₂ t₂) = .val b := by
  have lengths : (s₁.length = s₂.length) ↔ (t₁.length = t₂.length) := by
    rw [← related_length first, ← related_length second]
  by_cases types : type₁ = type₂
  · subst type₂
    by_cases tags : tag₁ = tag₂
    · subst tag₂
      by_cases same : s₁.length = s₂.length
      · have related := doEqList_related_of_values step first second b (by simpa [FlatSem.doEq, same] using result)
        simpa [ClosSem.doEq, lengths.mp same] using related
      · have targetDifferent : t₁.length ≠ t₂.length := fun h => same (lengths.mpr h)
        simpa [FlatSem.doEq, FlatSem.ctorSameType, ClosSem.doEq, same, targetDifferent] using result
    · simpa [FlatSem.doEq, FlatSem.ctorSameType, ClosSem.doEq, tags] using result
  · simp [FlatSem.doEq, FlatSem.ctorSameType, types] at result

end Flapjack.Compiler.Backend.FlatToClos
