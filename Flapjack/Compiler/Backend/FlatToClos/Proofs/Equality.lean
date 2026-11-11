module

public import Flapjack.Compiler.Backend.FlatToClos.Proofs.ValueRelation
public import Flapjack.Compiler.Backend.Semantics.FlatSem.Operations
public import Mathlib.Data.List.Forall2

@[expose] public section

/-! Proof-side facts for polymorphic equality during flat-to-closure lowering. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL

/-- Successful comparisons of these two source values agree for every pair
of related closure values. -/
def ValueComparisonSim (s₁ s₂ : FlatSem.Value) : Prop :=
  ∀ t₁ t₂ b, ValueRel s₁ t₁ → ValueRel s₂ t₂ →
    FlatSem.doEq s₁ s₂ = .val b → ClosSem.doEq t₁ t₂ = .val b

/-- The analogous comparison invariant for two fixed source lists. -/
def ListComparisonSim (s₁ s₂ : List FlatSem.Value) : Prop :=
  ∀ t₁ t₂ b, List.Forall₂ ValueRel s₁ t₁ → List.Forall₂ ValueRel s₂ t₂ →
    FlatSem.doEqList s₁ s₂ = .val b → ClosSem.doEqList t₁ t₂ = .val b

/-- Successful tagged-constructor comparison is preserved when the field-list comparison is preserved. A source type error is not assumed to
have a corresponding target result. -/
theorem doEq_con_related_of_lists
    {s₁ s₂ : List FlatSem.Value} {t₁ t₂ : List ClosSem.Value}
    (step : ListComparisonSim s₁ s₂)
    (first : List.Forall₂ ValueRel s₁ t₁) (second : List.Forall₂ ValueRel s₂ t₂)
    (tag₁ tag₂ : FlatLang.CtorId) (type₁ type₂ : FlatLang.TypeId) (b : Bool)
    (result : FlatSem.doEq (.conv (some (tag₁, type₁)) s₁)
      (.conv (some (tag₂, type₂)) s₂) = .val b) :
    ClosSem.doEq (.block tag₁ t₁) (.block tag₂ t₂) = .val b := by
  have lengths : (s₁.length = s₂.length) ↔ (t₁.length = t₂.length) := by
    rw [← first.length_eq, ← second.length_eq]
  by_cases types : type₁ = type₂
  · subst type₂
    by_cases tags : tag₁ = tag₂
    · subst tag₂
      by_cases same : s₁.length = s₂.length
      · have related := step t₁ t₂ b first second (by simpa [FlatSem.doEq, same] using result)
        simpa [ClosSem.doEq, lengths.mp same] using related
      · have targetDifferent : t₁.length ≠ t₂.length := fun h => same (lengths.mpr h)
        simpa [FlatSem.doEq, FlatSem.ctorSameType, ClosSem.doEq, same, targetDifferent] using result
    · simpa [FlatSem.doEq, FlatSem.ctorSameType, ClosSem.doEq, tags] using result
  · simp [FlatSem.doEq, FlatSem.ctorSameType, types] at result

/-- Related locations preserve every successful source comparison. -/
theorem valueComparisonSim_locations (flag₁ flag₂ : Bool) (index₁ index₂ : Nat) :
    ValueComparisonSim (.loc flag₁ index₁) (.loc flag₂ index₂) := by
  intro t₁ t₂ b first second result
  cases first
  cases second
  simp_all [FlatSem.doEq, ClosSem.doEq, Bool.beq_eq_decide_eq]

/-- Related literals preserve every successful comparison. -/
theorem valueComparisonSim_literals (left right : Flapjack.AstHOL.Lit) :
    ValueComparisonSim (.litv left) (.litv right) := by
  intro t₁ t₂ b first second result
  cases left <;> cases right <;> cases first <;> cases second <;>
    simp_all [FlatSem.doEq, ClosSem.doEq, Flapjack.SemanticPrimitivesHOL.litSameType,
      Int.natCast_inj, BitVec.toNat_inj, Flapjack.Basis.Pure.MlString.MlString.explode]
  rename_i left right
  cases left
  cases right
  simpa using result

/-- Constructor comparisons that do not recurse preserve every successful
result, including unequal tags and field-list lengths. -/
theorem valueComparisonSim_conv_no_rec
    (a b : Option (FlatLang.CtorId × FlatLang.TypeId)) (xs ys : List FlatSem.Value)
    (different : ¬(a = b ∧ xs.length = ys.length)) :
    ValueComparisonSim (.conv a xs) (.conv b ys) := by
  intro t₁ t₂ v first second result
  cases a with
  | none =>
    cases b with
    | none =>
      cases first with
      | tuple first =>
        cases second with
        | tuple second =>
          have len₁ := first.length_eq
          have len₂ := second.length_eq
          simp_all [FlatSem.doEq, FlatSem.ctorSameType, ClosSem.doEq]
    | some stamp => simp [FlatSem.doEq, FlatSem.ctorSameType] at result
  | some stamp₁ =>
    cases b with
    | none => simp [FlatSem.doEq, FlatSem.ctorSameType] at result
    | some stamp₂ =>
      obtain ⟨tag₁, type₁⟩ := stamp₁
      obtain ⟨tag₂, type₂⟩ := stamp₂
      cases first with
      | con first =>
        cases second with
        | con second =>
          have len₁ := first.length_eq
          have len₂ := second.length_eq
          by_cases tags : tag₁ = tag₂ <;> by_cases types : type₁ = type₂ <;>
            simp_all [FlatSem.doEq, FlatSem.ctorSameType, ClosSem.doEq]

/-- Unequal vector lengths determine the comparison without inspecting elements. -/
theorem valueComparisonSim_vector_no_rec (xs ys : List FlatSem.Value)
    (different : xs.length ≠ ys.length) : ValueComparisonSim (.vectorv xs) (.vectorv ys) := by
  intro t₁ t₂ b first second result
  cases first with
  | vector first =>
    cases second with
    | vector second =>
      have len₁ := first.length_eq
      have len₂ := second.length_eq
      simp_all [FlatSem.doEq, ClosSem.doEq]

/-- Successful polymorphic equality comparisons are preserved for related
values and lists. This is the unnamed equality subgoal in HOL's `op_eq_gc`
proof, so it has no separate HOL declaration. -/
theorem doEq_simulation :
    (∀ a b, ValueComparisonSim a b) ∧ (∀ xs ys, ListComparisonSim xs ys) := by
  refine FlatSem.doEq.mutual_induct ValueComparisonSim ListComparisonSim ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b _; exact valueComparisonSim_literals a b
  · intro a b _; exact valueComparisonSim_literals a b
  · intro a x b y _; exact valueComparisonSim_locations a b x y
  · intro a x b y _; exact valueComparisonSim_locations a b x y
  · intro a xs b ys _ ih
    cases a with
    | none =>
      cases b with
      | none =>
        intro t₁ t₂ result first second run
        cases first with
        | tuple first =>
          cases second with
          | tuple second =>
            exact doEq_con_related_of_lists ih first second 0 0 none none result
              (by simpa [FlatSem.doEq, FlatSem.ctorSameType] using run)
      | some stamp =>
        intro t₁ t₂ result first second h
        simp [FlatSem.doEq, FlatSem.ctorSameType] at h
    | some stamp₁ =>
      cases b with
      | none =>
        intro t₁ t₂ result first second h
        simp [FlatSem.doEq, FlatSem.ctorSameType] at h
      | some stamp₂ =>
        obtain ⟨tag₁, type₁⟩ := stamp₁
        obtain ⟨tag₂, type₂⟩ := stamp₂
        intro t₁ t₂ result first second run
        cases first with
        | con first =>
          cases second with
          | con second =>
            exact doEq_con_related_of_lists ih first second tag₁ tag₂ type₁ type₂ result run
  · intro a xs b ys diff _; exact valueComparisonSim_conv_no_rec a b xs ys diff
  · intro a xs b ys diff _; exact valueComparisonSim_conv_no_rec a b xs ys diff
  · intro xs ys _ ih t₁ t₂ result first second run
    cases first with
    | vector first =>
      cases second with
      | vector second =>
        exact doEq_con_related_of_lists ih first second 0 0 none none result
          (by simpa [FlatSem.doEq, FlatSem.ctorSameType] using run)
  · intro xs ys diff; exact valueComparisonSim_vector_no_rec xs ys diff
  · intro a n body b m body₂ t₁ t₂ result first second run
    cases first
    cases second
    simpa [FlatSem.doEq, ClosSem.doEq] using run
  · intro a n body b funs m t₁ t₂ result first second run
    cases first
    cases second
    simpa [FlatSem.doEq, ClosSem.doEq] using run
  · intro a funs n b m body t₁ t₂ result first second run
    cases first
    cases second
    simpa [FlatSem.doEq, ClosSem.doEq] using run
  · intro a funs₁ n b funs₂ m t₁ t₂ result first second run
    cases first
    cases second
    simpa [FlatSem.doEq, ClosSem.doEq] using run
  · intro left right noLit noLoc noCon noVector noCC noCR noRC noRR target₁ target₂ b first second result
    cases left <;> cases right
    all_goals first
      | exact False.elim (noLit _ _ rfl rfl)
      | exact False.elim (noLoc _ _ _ _ rfl rfl)
      | exact False.elim (noCon _ _ _ _ rfl rfl)
      | exact False.elim (noVector _ _ rfl rfl)
      | exact False.elim (noCC _ _ _ _ _ _ rfl rfl)
      | exact False.elim (noCR _ _ _ _ _ _ rfl rfl)
      | exact False.elim (noRC _ _ _ _ _ _ rfl rfl)
      | exact False.elim (noRR _ _ _ _ _ _ rfl rfl)
      | simp [FlatSem.doEq] at result
  · intro t₁ t₂ b first second result
    cases first
    cases second
    simpa [FlatSem.doEqList, ClosSem.doEqList] using result
  · intro x xs y ys h ih t₁ t₂ b first second result
    cases first with
    | cons head tail =>
      cases second with
      | cons head₂ tail₂ =>
        have targetEq := ih _ _ false head head₂ h
        simpa [FlatSem.doEqList, ClosSem.doEqList, h, targetEq] using result
  · intro x xs y ys h ih tail t₁ t₂ b first second result
    cases first with
    | cons head rest =>
      cases second with
      | cons head₂ rest₂ =>
        have targetEq := ih _ _ true head head₂ h
        simp only [FlatSem.doEqList, h] at result
        simpa [ClosSem.doEqList, targetEq] using tail _ _ b rest rest₂ result
  · intro x xs y ys h _ t₁ t₂ b first second result
    simp [FlatSem.doEqList, h] at result
  · intro first second nonempty noCons
    cases first with
    | nil =>
      cases second with
      | nil => exact False.elim (nonempty rfl rfl)
      | cons y ys =>
        intro t₁ t₂ b related₁ related₂ result
        cases related₁
        cases related₂
        simpa [FlatSem.doEqList, ClosSem.doEqList] using result
    | cons x xs =>
      cases second with
      | nil =>
        intro t₁ t₂ b related₁ related₂ result
        cases related₁
        cases related₂
        simpa [FlatSem.doEqList, ClosSem.doEqList] using result
      | cons y ys => exact False.elim (noCons x xs y ys rfl rfl)

end Flapjack.Compiler.Backend.FlatToClos
