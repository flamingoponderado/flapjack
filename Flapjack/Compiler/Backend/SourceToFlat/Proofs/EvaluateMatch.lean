module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PatternRows
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateControl
public import Flapjack.Compiler.Backend.FlatProps.EvaluateMatch

@[expose] public section

/-! Connecting source row selection to source evaluation. These Flapjack
helpers use the full clocked evaluator but are not HOL theorem ports. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL

/-- Interpret source row selection through the clocked evaluator, which also
checks distinct bindings for each row it visits. -/
theorem evaluateMatch_of_sourcePmatchRows {F : Type} (st : State F) (env : SemEnv Value)
    (value errorValue : Value) (rows : List (Pat × AstHOL.Exp)) :
    let run := EvaluateHOL.evaluateMatch st env value rows errorValue
    match sourcePmatchRows env st value rows with
    | .typeError => run = (st, .err (.abort .typeError))
    | .noMatch =>
      (∀ next, run ≠ (next, .err (.abort .typeError))) → run = (st, .err (.raise errorValue))
    | .match (bindings, pattern, body) =>
      (∀ next, run ≠ (next, .err (.abort .typeError))) → (patBindings pattern).Nodup ∧
        run = EvaluateHOL.evaluate st { env with v := nsAppend (alistToNs bindings) env.v } [body] := by
  induction rows with
  | nil => simp [sourcePmatchRows, EvaluateHOL.evaluateMatch]
  | cons row rest ih =>
    obtain ⟨pattern, body⟩ := row
    by_cases distinct : (patBindings pattern).Nodup
    · cases matched : pmatch env.c st.refs pattern value [] with
      | noMatch => simpa [sourcePmatchRows, EvaluateHOL.evaluateMatch, distinct, matched] using ih
      | typeError => simp [sourcePmatchRows, EvaluateHOL.evaluateMatch, distinct, matched, EvaluateHOL.typeError]
      | «match» bindings => simp [sourcePmatchRows, EvaluateHOL.evaluateMatch, distinct, matched]
    · have bad : EvaluateHOL.evaluateMatch st env value ((pattern, body) :: rest) errorValue =
          (st, .err (.abort .typeError)) := by
        simp [EvaluateHOL.evaluateMatch, distinct, EvaluateHOL.typeError]
      simp only [bad]
      cases sourcePmatchRows env st value ((pattern, body) :: rest) with
      | typeError => trivial
      | noMatch => intro safe; exact (safe st rfl).elim
      | «match» selected =>
        obtain ⟨bindings, selectedPattern, selectedBody⟩ := selected
        intro safe
        exact (safe st rfl).elim

end Flapjack.Compiler.Backend.SourceToFlat
