import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationDeclarations
import Flapjack.Compiler.Backend.SourceEval.Proofs.PatternMatchSafety
import Flapjack.EvaluateProps.Length

/-! Value-declaration case of the source evaluator simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.EvaluateHOL

/-- Value declarations preserve the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_Dlet {Config F A : Type} [Nonempty A] (ci : CompilerInstance Config) (s : State F)
    (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs) (pat : Pat) (expr : Flapjack.AstHOL.Exp)
    (ih : (patBindings pat).Nodup ∧ everyExp (oneConCheck env.c) expr = true →
      ExpsSimAt (A := A) ci s env [expr]) : DecsSimAt ci s env [.dlet loc pat expr] := by
  intro s' res t env' ⟨run, related, envRelated, safe⟩
  have constructors : env.c = env'.c := envRelated.1
  by_cases guard : (decide (patBindings pat).Nodup && everyExp (oneConCheck env.c) expr) = true
  · have guardParts : (patBindings pat).Nodup ∧ everyExp (oneConCheck env.c) expr = true := by
      simpa using guard
    have targetGuard : (decide (patBindings pat).Nodup && everyExp (oneConCheck env'.c) expr) = true := by
      simpa [constructors] using guard
    rw [evaluateDecs] at run
    simp only [guard, ↓reduceIte] at run
    cases exprRun : evaluate s env [expr] with
    | mk middle exprResult =>
      cases exprResult with
      | err error =>
        simp only [exprRun] at run
        cases run
        have exprSafe : (Result.err error : Result (List Value) Value) ≠ .err (.abort .typeError) := by
          intro eq
          cases eq
          exact safe rfl
        obtain ⟨es₁, t₁, r₁, targetRun, stateRel₁, esEq, resultRel₁, fwd, stack⟩ :=
          ih guardParts s' (.err error) (Classical.choice inferInstance) t env'
            ⟨exprRun, related, envRelated, exprSafe⟩
        cases r₁ with
        | val values => cases resultRel₁
        | err targetErr =>
          refine ⟨es₁, t₁, .err targetErr, ?_, stateRel₁, esEq, resultRel₁, fwd, ?_⟩
          · simp [evaluateDecs, targetGuard, targetRun]
          · intro notAbort
            apply stack
            cases targetErr with
            | raise value => simp [abort]
            | abort why => exact (notAbort (by simp [abort])).elim
      | val values =>
        simp only [exprRun] at run
        obtain ⟨es₁, t₁, r₁, targetRun, stateRel₁, esEq, resultRel₁, fwd, stack⟩ :=
          ih guardParts middle (.val values) (Classical.choice inferInstance) t env'
            ⟨exprRun, related, envRelated, by simp⟩
        cases r₁ with
        | err err => cases resultRel₁
        | val values' =>
          have vsRel : List.Forall₂ (ValueRel es₁) values values' := resultRel₁
          obtain ⟨head, valuesEq⟩ := Flapjack.EvaluateProps.evaluateSingFull s env expr middle values exprRun
          subst values
          cases vsRel with
          | @cons _ targetHead _ _ headRel tailRel =>
            cases tailRel with
            | nil =>
              have envRelated₁ : envRel (ValueRel es₁) env env' :=
                (forwardRules (oracleState t.evalState) (.conv none []) (.conv none []) es₁ [] [] env env').2.2.1
                  ⟨envRelated, fwd⟩
              have matchRelated := pmatchDrule env middle pat (headValue [head])
                (pmatch env.c middle.refs pat (headValue [head]) []) ci t₁ env' (headValue [targetHead])
                ⟨rfl, stateRel₁, by simpa [esEq] using envRelated₁,
                  by simpa [esEq, headValue, Flapjack.holHd] using headRel⟩
              cases matched : pmatch env.c middle.refs pat (headValue [head]) [] with
              | typeError =>
                simp [matched, typeError] at run
                obtain ⟨_, rfl⟩ := run
                exact (safe rfl).elim
              | noMatch =>
                simp only [matched] at run
                obtain ⟨stateEq, resultEq⟩ := Prod.mk.inj run
                subst s'
                subst res
                have targetMatch : pmatch env'.c t₁.refs pat (headValue [targetHead]) [] = .noMatch := by
                  simpa [matched, matchResultRel] using matchRelated
                refine ⟨es₁, t₁, .err (.raise bindExnV), ?_, stateRel₁, esEq, ?_, fwd, ?_⟩
                · simp [evaluateDecs, targetGuard, targetRun, targetMatch]
                · exact ValueRel.con .nil
                · intro _
                  exact stack (by simp [abort])
              | «match» bindings =>
                simp only [matched] at run
                obtain ⟨stateEq, resultEq⟩ := Prod.mk.inj run
                subst s'
                subst res
                obtain ⟨bindings', targetMatch, bindingsRel⟩ := by
                  simpa [matched, matchResultRel] using matchRelated
                refine ⟨es₁, t₁, .val { v := alistToNs bindings', c := nsEmpty }, ?_, stateRel₁, esEq, ?_, fwd, ?_⟩
                · simp [evaluateDecs, targetGuard, targetRun, targetMatch]
                · change envRel (ValueRel es₁) { v := alistToNs bindings, c := nsEmpty }
                    { v := alistToNs bindings', c := nsEmpty }
                  have base : envRel (ValueRel es₁) ({ v := nsEmpty, c := nsEmpty } : SemEnv Value)
                      ({ v := nsEmpty, c := nsEmpty } : SemEnv Value) := by simp [envRel, nsLookup_nsEmpty]
                  have bound := envRel_add_nsBindList (ValueRel es₁) ({ v := nsEmpty, c := nsEmpty } : SemEnv Value)
                    nsEmpty ({ v := nsEmpty, c := nsEmpty } : SemEnv Value) nsEmpty bindings bindings' ⟨base, by simpa [esEq] using bindingsRel⟩
                  simpa [← nsAppend_to_nsBindList, alistToNs, nsAppend, nsEmpty] using bound
                · intro _
                  exact stack (by simp [abort])
  · simp [evaluateDecs, guard, typeError] at run
    obtain ⟨_, rfl⟩ := run
    exact (safe rfl).elim
end Flapjack.Compiler.Backend.SourceEval.Proofs
