module

public import Flapjack.Compiler.Inference.Unify.ComputationalWf.Insert
public import Flapjack.Compiler.Inference.Unify.ComputationalWalk.ToVar
public import Flapjack.Compiler.Inference.Unify.Occurs.WorklistTotal

@[expose] public section

/-! The source paired-list unifier's single tail-recursive step. -/
namespace Flapjack.Compiler.Inference.Unify

/-- Source-shaped unifier step using selected total walkers. It is untagged:
    HOL's tail-recursive choices can differ on non-well-formed substitutions. -/
noncomputable def cunifyCodeModel :
    Spt InferT × List (List InferT × List InferT) →
      Sum (Spt InferT × List (List InferT × List InferT)) (Option (Spt InferT))
  | (s, []) => .inr (some s)
  | (s, ([], []) :: rest) => .inl (s, rest)
  | (_, ([], _ :: _) :: _) | (_, (_ :: _, []) :: _) => .inr none
  | (s, (a :: left, b :: right) :: rest) =>
    match tcwalkModel s a, tcwalkModel s b with
    | .uvar x, .uvar y => .inl (if x = y then s else sptInsert x (.uvar y) s, (left, right) :: rest)
    | .uvar x, .varDb y | .varDb y, .uvar x => .inl (sptInsert x (.varDb y) s, (left, right) :: rest)
    | .uvar x, .app ts name | .app ts name, .uvar x =>
      if tcocwlModel s x [ts] then .inr none
      else .inl (sptInsert x (.app ts name) s, (left, right) :: rest)
    | .varDb x, .varDb y => if x = y then .inl (s, (left, right) :: rest) else .inr none
    | .app xs x, .app ys y => if x = y then .inl (s, (xs, ys) :: (left, right) :: rest) else .inr none
    | _, _ => .inr none

/-- Every source-shaped continuing step preserves the original cwfs guard. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "kcunifywl_preserves_precond"]
theorem kcunifywlPreservesPrecondModel : ∀ x y,
    (fun p : Spt InferT × List (List InferT × List InferT) => cwfs p.1) x ∧
      cunifyCodeModel x = .inl y →
    (fun p : Spt InferT × List (List InferT × List InferT) => cwfs p.1) y := by
  rintro ⟨s, work⟩ ⟨out, next⟩ ⟨hw, step⟩
  cases work with
  | nil => simp [cunifyCodeModel] at step
  | cons pair rest =>
    obtain ⟨left, right⟩ := pair
    cases left with
    | nil =>
      cases right with
      | nil =>
        simp [cunifyCodeModel] at step
        cases step.1
        exact hw
      | cons b bs => simp [cunifyCodeModel] at step
    | cons a as' =>
      cases right with
      | nil => simp [cunifyCodeModel] at step
      | cons b bs =>
        cases ha : tcwalkModel s a <;> cases hb : tcwalkModel s b <;>
          simp only [cunifyCodeModel, ha, hb] at step
        case varDb.varDb | app.app =>
          split at step <;> simp_all
        case varDb.app | app.varDb => simp at step
        case varDb.uvar =>
          rename_i db v
          simp only [Sum.inl.injEq, Prod.mk.injEq] at step
          rcases step with ⟨rfl, _⟩
          exact cwfsInsertTvarDb s v db ⟨(tcwalkEqInferTuvarModel s b v ⟨hw, hb⟩).1, hw⟩
        case uvar.varDb =>
          rename_i v db
          simp only [Sum.inl.injEq, Prod.mk.injEq] at step
          rcases step with ⟨rfl, _⟩
          exact cwfsInsertTvarDb s v db ⟨(tcwalkEqInferTuvarModel s a v ⟨hw, ha⟩).1, hw⟩
        case app.uvar =>
          rename_i ts tc v
          cases ho : tcocwlModel s v [ts] <;> simp only [ho, Bool.false_eq_true, ↓reduceIte,
            Sum.inl.injEq, Prod.mk.injEq] at step
          · rcases step with ⟨rfl, _⟩
            exact cwfsInsertAppOfOccursFalse s v tc ts
              ⟨(tcwalkEqInferTuvarModel s b v ⟨hw, hb⟩).1, hw, by
                rw [occursWorkListMatchesModel s v ts hw, ho]⟩
          · simp at step
        case uvar.app =>
          rename_i v ts tc
          cases ho : tcocwlModel s v [ts] <;> simp only [ho, Bool.false_eq_true, ↓reduceIte,
            Sum.inl.injEq, Prod.mk.injEq] at step
          · rcases step with ⟨rfl, _⟩
            exact cwfsInsertAppOfOccursFalse s v tc ts
              ⟨(tcwalkEqInferTuvarModel s a v ⟨hw, ha⟩).1, hw, by
                rw [occursWorkListMatchesModel s v ts hw, ho]⟩
          · simp at step
        case uvar.uvar =>
          rename_i v1 v2
          by_cases eq : v1 = v2
          · simp [eq] at step
            cases step.1
            exact hw
          · simp [eq] at step
            rcases step with ⟨rfl, _⟩
            exact cwfsVar2Extend s v1 v2 ⟨hw, eq,
              (tcwalkEqInferTuvarModel s a v1 ⟨hw, ha⟩).1,
              (tcwalkEqInferTuvarModel s b v2 ⟨hw, hb⟩).1⟩

end Flapjack.Compiler.Inference.Unify
