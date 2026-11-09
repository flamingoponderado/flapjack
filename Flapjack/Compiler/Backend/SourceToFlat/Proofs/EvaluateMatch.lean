module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PatternRows
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateControl
public import Flapjack.Compiler.Backend.FlatProps.EvaluateMatch

@[expose] public section

/-! Connecting source row selection to source evaluation. These Flapjack
helpers use the full clocked evaluator but are not HOL theorem ports. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL

/-- If source matching selects no row and does not type-error, evaluation
re-raises the designated fallback value. -/
theorem evaluateMatch_noMatch {F : Type} (st : State F) (env : SemEnv Value)
    (value errorValue : Value) (rows : List (Pat × AstHOL.Exp))
    (safe : ∀ next, EvaluateHOL.evaluateMatch st env value rows errorValue ≠
      (next, .err (.abort .typeError)))
    (selected : sourcePmatchRows env st value rows = .noMatch) :
    EvaluateHOL.evaluateMatch st env value rows errorValue = (st, .err (.raise errorValue)) := by
  induction rows with
  | nil => simp [EvaluateHOL.evaluateMatch]
  | cons row rest ih =>
    obtain ⟨pattern, body⟩ := row
    by_cases unique : (patBindings pattern).Nodup
    · cases matching : pmatch env.c st.refs pattern value [] with
      | typeError => simp [sourcePmatchRows, matching] at selected
      | «match» bindings => simp [sourcePmatchRows, matching] at selected
      | noMatch =>
        have restSafe : ∀ next, EvaluateHOL.evaluateMatch st env value rest errorValue ≠
            (next, .err (.abort .typeError)) := by
          intro next bad
          apply safe next
          simpa [EvaluateHOL.evaluateMatch, unique, matching] using bad
        have restSelected : sourcePmatchRows env st value rest = .noMatch := by
          simpa [sourcePmatchRows, matching] using selected
        simpa [EvaluateHOL.evaluateMatch, unique, matching] using ih restSafe restSelected
    · have bad : EvaluateHOL.evaluateMatch st env value ((pattern, body) :: rest) errorValue =
          (st, .err (.abort .typeError)) := by
        simp [EvaluateHOL.evaluateMatch, unique, EvaluateHOL.typeError]
      exact (safe st bad).elim

/-- If source matching selects a row and does not type-error, its bindings
are distinct and evaluation runs the selected body in the extended namespace. -/
theorem evaluateMatch_selected {F : Type} (st : State F) (env : SemEnv Value)
    (value errorValue : Value) (rows : List (Pat × AstHOL.Exp))
    (bindings : List (VarN × Value)) (pattern : Pat) (body : AstHOL.Exp)
    (safe : ∀ next, EvaluateHOL.evaluateMatch st env value rows errorValue ≠
      (next, .err (.abort .typeError)))
    (selected : sourcePmatchRows env st value rows = .match (bindings, pattern, body)) :
    (patBindings pattern).Nodup ∧
      EvaluateHOL.evaluateMatch st env value rows errorValue =
        EvaluateHOL.evaluate st { env with v := nsAppend (alistToNs bindings) env.v } [body] := by
  induction rows with
  | nil => simp [sourcePmatchRows] at selected
  | cons row rest ih =>
    obtain ⟨headPattern, headBody⟩ := row
    by_cases unique : (patBindings headPattern).Nodup
    · cases matching : pmatch env.c st.refs headPattern value [] with
      | typeError => simp [sourcePmatchRows, matching] at selected
      | noMatch =>
        have restSafe : ∀ next, EvaluateHOL.evaluateMatch st env value rest errorValue ≠
            (next, .err (.abort .typeError)) := by
          intro next bad
          apply safe next
          simpa [EvaluateHOL.evaluateMatch, unique, matching] using bad
        have restSelected : sourcePmatchRows env st value rest = .match (bindings, pattern, body) := by
          simpa [sourcePmatchRows, matching] using selected
        obtain ⟨distinct, run⟩ := ih restSafe restSelected
        exact ⟨distinct, by simpa [EvaluateHOL.evaluateMatch, unique, matching] using run⟩
      | «match» bound =>
        simp only [sourcePmatchRows, matching, MatchResult.match.injEq, Prod.mk.injEq] at selected
        obtain ⟨rfl, rfl, rfl⟩ := selected
        exact ⟨unique, by simp [EvaluateHOL.evaluateMatch, unique, matching]⟩
    · have bad : EvaluateHOL.evaluateMatch st env value ((headPattern, headBody) :: rest) errorValue =
          (st, .err (.abort .typeError)) := by
        simp [EvaluateHOL.evaluateMatch, unique, EvaluateHOL.typeError]
      exact (safe st bad).elim

/-- The flat evaluator's row selection and selected-body evaluation. This
helper factors the common behavior of flat `handle` and `mat`. -/
noncomputable def flatEvaluateMatch {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state : FlatSem.State C F) (value errorValue : FlatSem.Value)
    (rows : List (FlatLang.Pat × FlatLang.Exp)) : FlatSem.EvalResult C F :=
  match FlatSem.selectRow state rows value errorValue with
  | .error error => (state, .err error)
  | .ok (bindings, body) => FlatSem.evaluate { env with v := bindings ++ env.v } state [body]

/-- The simulation helper is the source flat-properties match evaluator. -/
theorem flatEvaluateMatch_eq_flatProps {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state : FlatSem.State C F) (value errorValue : FlatSem.Value)
    (rows : List (FlatLang.Pat × FlatLang.Exp)) :
    flatEvaluateMatch env state value errorValue rows = FlatProps.evaluateMatch env state value rows errorValue := by
  unfold flatEvaluateMatch FlatSem.selectRow FlatProps.evaluateMatch
  cases FlatSem.pmatchRows rows state value with
  | typeError => rfl
  | noMatch => rfl
  | «match» matchResult =>
    rcases matchResult with ⟨bindings, pattern, body⟩
    by_cases unique : (FlatLang.patBindings pattern).Nodup <;> simp [unique]

end Flapjack.Compiler.Backend.SourceToFlat
