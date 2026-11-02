import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateClock

/-! Source-shaped clauses of the flat evaluator. These equations do not by
themselves establish correspondence for the remaining evaluator clauses. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.SemanticPrimitivesHOL

/-- The empty expression-list case of the source evaluator. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "evaluate_def" 815]
theorem evaluate_nil_source {C F : Type} (env : Environment Value) (state : State C F) :
    evaluate env state [] = (state, .val []) := by
  rw [evaluate]

/-- The empty declaration-list case of the source evaluator. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "evaluate_def" 815]
theorem evaluateDecs_nil_source {C F : Type} (state : State C F) :
    evaluateDecs state [] = (state, none) := by
  rw [evaluateDecs]

/-- Declaration lists apply the source clock clamp before continuing. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "evaluate_def" 815]
theorem evaluateDecs_cons_source {C F : Type} (state : State C F)
    (declaration : FlatLang.Exp) (rest : List FlatLang.Exp) :
    evaluateDecs state (declaration :: rest) =
      match fixClock state (evaluateDec state declaration) with
      | (next, none) => evaluateDecs next rest
      | (next, some error) => (next, some error) := by
  rw [(fixClock_evaluations ⟨[]⟩ state [declaration] declaration rest).2.1]
  exact evaluateDecs_cons state declaration rest

open Classical in
/-- A declaration succeeds precisely when its expression returns unit. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "evaluate_def" 815]
theorem evaluateDec_source {C F : Type} (state : State C F) (declaration : FlatLang.Exp) :
    evaluateDec state declaration =
      match evaluate ⟨[]⟩ state [declaration] with
      | (next, .val values) =>
          if values = [unitValue] then (next, none) else (next, some (.abort .typeError))
      | (next, .err error) => (next, some error) := by
  unfold evaluateDec
  generalize evaluate ⟨[]⟩ state [declaration] = evaluated
  obtain ⟨next, result⟩ := evaluated
  cases result with
  | err error => rfl
  | val values =>
    dsimp only
    split <;> simp_all [unitValue]

end Flapjack.Compiler.Backend.FlatSem
