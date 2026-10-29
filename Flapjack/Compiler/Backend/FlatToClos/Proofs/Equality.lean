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

/-- Successful comparisons of these two source values agree for every pair
of related closure values. -/
def ValueComparisonSim (s₁ s₂ : FlatSem.Value) : Prop :=
  ∀ t₁ t₂ b, ValueRel s₁ t₁ → ValueRel s₂ t₂ →
    FlatSem.doEq s₁ s₂ = .val b → ClosSem.doEq t₁ t₂ = .val b

/-- The analogous comparison invariant for two fixed source lists. -/
def ListComparisonSim (s₁ s₂ : List FlatSem.Value) : Prop :=
  ∀ t₁ t₂ b, List.Forall₂ ValueRel s₁ t₁ → List.Forall₂ ValueRel s₂ t₂ →
    FlatSem.doEqList s₁ s₂ = .val b → ClosSem.doEqList t₁ t₂ = .val b

/-- The cons case composes only the head and tail induction hypotheses. -/
theorem listComparisonSim_cons {s₁ s₂ : FlatSem.Value} {xs ys : List FlatSem.Value}
    (headSim : ValueComparisonSim s₁ s₂) (tailSim : ListComparisonSim xs ys) :
    ListComparisonSim (s₁ :: xs) (s₂ :: ys) := by
  intro t₁ t₂ b first second result
  cases first with
  | cons head tail =>
    cases second with
    | cons head₂ tail₂ =>
      cases h : FlatSem.doEq s₁ s₂ with
      | typeError => simp [FlatSem.doEqList, h] at result
      | val value =>
        have targetEq := headSim _ _ value head head₂ h
        cases value with
        | false => simpa [FlatSem.doEqList, ClosSem.doEqList, h, targetEq] using result
        | true =>
          simp only [FlatSem.doEqList, h] at result
          simpa [ClosSem.doEqList, targetEq] using tailSim _ _ b tail tail₂ result

/-- Empty and unequal-length list cases need no element hypothesis. -/
theorem listComparisonSim_nil_nil : ListComparisonSim [] [] := by
  intro t₁ t₂ b first second result
  cases first
  cases second
  simpa [FlatSem.doEqList, ClosSem.doEqList] using result

theorem listComparisonSim_nil_cons (head : FlatSem.Value) (tail : List FlatSem.Value) :
    ListComparisonSim [] (head :: tail) := by
  intro t₁ t₂ b first second result
  cases first
  cases second
  simpa [FlatSem.doEqList, ClosSem.doEqList] using result

theorem listComparisonSim_cons_nil (head : FlatSem.Value) (tail : List FlatSem.Value) :
    ListComparisonSim (head :: tail) [] := by
  intro t₁ t₂ b first second result
  cases first
  cases second
  simpa [FlatSem.doEqList, ClosSem.doEqList] using result

private theorem related_length {source : List FlatSem.Value} {target : List ClosSem.Value}
    (related : List.Forall₂ ValueRel source target) : source.length = target.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Successful vector comparison is preserved when the field-list comparison is preserved. -/
theorem doEq_vector_related_of_lists
    {s₁ s₂ : List FlatSem.Value} {t₁ t₂ : List ClosSem.Value}
    (step : ListComparisonSim s₁ s₂)
    (first : List.Forall₂ ValueRel s₁ t₁) (second : List.Forall₂ ValueRel s₂ t₂)
    (b : Bool) (result : FlatSem.doEq (.vectorv s₁) (.vectorv s₂) = .val b) :
    ClosSem.doEq (.block 0 t₁) (.block 0 t₂) = .val b := by
  have lengths : (s₁.length = s₂.length) ↔ (t₁.length = t₂.length) := by
    rw [← related_length first, ← related_length second]
  by_cases same : s₁.length = s₂.length
  · have related := step t₁ t₂ b first second (by simpa [FlatSem.doEq, same] using result)
    simpa [ClosSem.doEq, lengths.mp same] using related
  · have targetDifferent : t₁.length ≠ t₂.length := fun h => same (lengths.mpr h)
    simpa [FlatSem.doEq, ClosSem.doEq, same, targetDifferent] using result

/-- Successful tuple comparison is preserved when the field-list comparison is preserved. -/
theorem doEq_tuple_related_of_lists
    {s₁ s₂ : List FlatSem.Value} {t₁ t₂ : List ClosSem.Value}
    (step : ListComparisonSim s₁ s₂)
    (first : List.Forall₂ ValueRel s₁ t₁) (second : List.Forall₂ ValueRel s₂ t₂)
    (b : Bool) (result : FlatSem.doEq (.conv none s₁) (.conv none s₂) = .val b) :
    ClosSem.doEq (.block 0 t₁) (.block 0 t₂) = .val b := by
  have lengths : (s₁.length = s₂.length) ↔ (t₁.length = t₂.length) := by
    rw [← related_length first, ← related_length second]
  by_cases same : s₁.length = s₂.length
  · have related := step t₁ t₂ b first second (by simpa [FlatSem.doEq, same] using result)
    simpa [ClosSem.doEq, lengths.mp same] using related
  · have targetDifferent : t₁.length ≠ t₂.length := fun h => same (lengths.mpr h)
    simpa [FlatSem.doEq, FlatSem.ctorSameType, ClosSem.doEq, same, targetDifferent] using result

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
    rw [← related_length first, ← related_length second]
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

/-- Vector comparison uses exactly the invariant for its two element lists. -/
theorem valueComparisonSim_vector {xs ys : List FlatSem.Value}
    (fields : ListComparisonSim xs ys) : ValueComparisonSim (.vectorv xs) (.vectorv ys) := by
  intro t₁ t₂ b first second result
  cases first with
  | vector first =>
    cases second with
    | vector second => exact doEq_vector_related_of_lists fields first second b result

/-- Tuple comparison uses exactly the invariant for its two field lists. -/
theorem valueComparisonSim_tuple {xs ys : List FlatSem.Value}
    (fields : ListComparisonSim xs ys) : ValueComparisonSim (.conv none xs) (.conv none ys) := by
  intro t₁ t₂ b first second result
  cases first with
  | tuple first =>
    cases second with
    | tuple second => exact doEq_tuple_related_of_lists fields first second b result

/-- Tagged constructor comparison uses the invariant for its two field lists. -/
theorem valueComparisonSim_con {xs ys : List FlatSem.Value}
    (tag₁ tag₂ : FlatLang.CtorId) (type₁ type₂ : FlatLang.TypeId)
    (fields : ListComparisonSim xs ys) :
    ValueComparisonSim (.conv (some (tag₁, type₁)) xs) (.conv (some (tag₂, type₂)) ys) := by
  intro t₁ t₂ b first second result
  cases first with
  | con first =>
    cases second with
    | con second => exact doEq_con_related_of_lists fields first second tag₁ tag₂ type₁ type₂ b result

/-- Related locations preserve every successful source comparison. -/
theorem valueComparisonSim_locations (flag₁ flag₂ : Bool) (index₁ index₂ : Nat) :
    ValueComparisonSim (.loc flag₁ index₁) (.loc flag₂ index₂) := by
  intro t₁ t₂ b first second result
  cases first
  cases second
  simp_all [FlatSem.doEq, ClosSem.doEq, Bool.beq_eq_decide_eq]

/-- Related ordinary closures compare alike. -/
theorem valueComparisonSim_closures (env₁ env₂ : FlatSem.Environment FlatSem.Value)
    (name₁ name₂ : Flapjack.AstHOL.VarN) (body₁ body₂ : FlatLang.Exp) :
    ValueComparisonSim (.closure env₁ name₁ body₁) (.closure env₂ name₂ body₂) := by
  intro t₁ t₂ b first second result
  cases first
  cases second
  simpa [FlatSem.doEq, ClosSem.doEq] using result

/-- Related ordinary and recursive closures compare alike. -/
theorem valueComparisonSim_closure_rec (env₁ env₂ : FlatSem.Environment FlatSem.Value)
    (name₁ name₂ : Flapjack.AstHOL.VarN) (body : FlatLang.Exp)
    (funs : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp)) :
    ValueComparisonSim (.closure env₁ name₁ body) (.recclosure env₂ funs name₂) := by
  intro t₁ t₂ b first second result
  cases first
  cases second
  simpa [FlatSem.doEq, ClosSem.doEq] using result

/-- Related recursive and ordinary closures compare alike. -/
theorem valueComparisonSim_rec_closure (env₁ env₂ : FlatSem.Environment FlatSem.Value)
    (name₁ name₂ : Flapjack.AstHOL.VarN) (body : FlatLang.Exp)
    (funs : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp)) :
    ValueComparisonSim (.recclosure env₁ funs name₁) (.closure env₂ name₂ body) := by
  intro t₁ t₂ b first second result
  cases first
  cases second
  simpa [FlatSem.doEq, ClosSem.doEq] using result

/-- Related recursive closures compare alike. -/
theorem valueComparisonSim_rec_rec (env₁ env₂ : FlatSem.Environment FlatSem.Value)
    (name₁ name₂ : Flapjack.AstHOL.VarN)
    (funs₁ funs₂ : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp)) :
    ValueComparisonSim (.recclosure env₁ funs₁ name₁) (.recclosure env₂ funs₂ name₂) := by
  intro t₁ t₂ b first second result
  cases first
  cases second
  simpa [FlatSem.doEq, ClosSem.doEq] using result

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
          have len₁ := related_length first
          have len₂ := related_length second
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
          have len₁ := related_length first
          have len₂ := related_length second
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
      have len₁ := related_length first
      have len₂ := related_length second
      simp_all [FlatSem.doEq, ClosSem.doEq]

/-- A false head comparison terminates the list comparison. -/
theorem listComparisonSim_cons_false {s₁ s₂ : FlatSem.Value} {xs ys : List FlatSem.Value}
    (headSim : ValueComparisonSim s₁ s₂) (h : FlatSem.doEq s₁ s₂ = .val false) :
    ListComparisonSim (s₁ :: xs) (s₂ :: ys) := by
  intro t₁ t₂ b first second result
  cases first with
  | cons head tail =>
    cases second with
    | cons head₂ tail₂ =>
      have targetEq := headSim _ _ false head head₂ h
      simpa [FlatSem.doEqList, ClosSem.doEqList, h, targetEq] using result

/-- A source type error cannot be a successful list comparison. -/
theorem listComparisonSim_cons_error {s₁ s₂ : FlatSem.Value} {xs ys : List FlatSem.Value}
    (h : FlatSem.doEq s₁ s₂ = .typeError) : ListComparisonSim (s₁ :: xs) (s₂ :: ys) := by
  intro t₁ t₂ b first second result
  simp [FlatSem.doEqList, h] at result

/-- Successful polymorphic equality comparisons are preserved for related
values and lists. This proof-side statement awaits HOL correspondence review. -/
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
      | none => exact valueComparisonSim_tuple ih
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
        exact valueComparisonSim_con tag₁ tag₂ type₁ type₂ ih
  · intro a xs b ys diff _; exact valueComparisonSim_conv_no_rec a b xs ys diff
  · intro a xs b ys diff _; exact valueComparisonSim_conv_no_rec a b xs ys diff
  · intro xs ys _ ih; exact valueComparisonSim_vector ih
  · intro xs ys diff; exact valueComparisonSim_vector_no_rec xs ys diff
  · intro a n body b m body₂; exact valueComparisonSim_closures a b n m body body₂
  · intro a n body b funs m; exact valueComparisonSim_closure_rec a b n m body funs
  · intro a funs n b m body; exact valueComparisonSim_rec_closure a b n m body funs
  · intro a funs₁ n b funs₂ m; exact valueComparisonSim_rec_rec a b n m funs₁ funs₂
  · intro left right noLit noLoc noCon noVector noCC noCR noRC noRR
    intro target₁ target₂ b first second result
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
  · exact listComparisonSim_nil_nil
  · intro x xs y ys h ih; exact listComparisonSim_cons_false ih h
  · intro x xs y ys _ ih tail; exact listComparisonSim_cons ih tail
  · intro x xs y ys h _; exact listComparisonSim_cons_error h
  · intro first second nonempty noCons
    cases first with
    | nil =>
      cases second with
      | nil => exact False.elim (nonempty rfl rfl)
      | cons y ys => exact listComparisonSim_nil_cons y ys
    | cons x xs =>
      cases second with
      | nil => exact listComparisonSim_cons_nil x xs
      | cons y ys => exact False.elim (noCons x xs y ys rfl rfl)

end Flapjack.Compiler.Backend.FlatToClos
