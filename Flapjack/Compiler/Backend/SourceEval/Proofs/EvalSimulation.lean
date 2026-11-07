import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationApp
import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationBase
import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationCons
import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationConstructors
import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationDeclarations
import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationDecsCons
import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationDenv
import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationDlet
import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationExpressions
import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationHandle
import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationIf
import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationLet
import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationLetrec
import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationLog
import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationMat
import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationMatchCons
import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationModules
import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationStamps
import Flapjack.EvaluateHOL.Clock

/-! Mutual induction and complete source evaluator simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.EvaluateHOL

mutual
/-- Flapjack infrastructure: expression component of the mutual induction. -/
private theorem expsSimFull {Config F A : Type} [Nonempty A] (ci : CompilerInstance Config)
    (state : State F) (env : SemEnv Value) (exprs : List AstHOL.Exp) :
    ExpsSimAt (A := A) ci state env exprs := by
  cases exprs with
  | nil => exact evalSimulation_ExpsNil ci state env
  | cons first rest =>
    cases rest with
    | cons second tail =>
      apply evalSimulation_ExpsCons ci state env first second tail
      refine ⟨?_, expsSimFull ci state env [first]⟩
      intro middle outcome values ⟨run, rfl⟩
      have bound := evaluateClockFull state middle env [first] outcome run
      exact expsSimFull ci middle env (second :: tail)
    | nil =>
      cases first with
      | lit lit => exact evalSimulation_Lit ci state env lit
      | var name => exact evalSimulation_Var ci state env name
      | fn name body => exact evalSimulation_Fn ci state env name body
      | raise expr => exact evalSimulation_Raise ci state env expr (expsSimFull ci state env [expr])
      | tannot expr typ => exact evalSimulation_Tannot ci state env expr typ (expsSimFull ci state env [expr])
      | lannot expr loc => exact evalSimulation_Lannot ci state env expr loc (expsSimFull ci state env [expr])
      | con name args =>
        apply evalSimulation_Con ci state env name args
        intro _
        exact expsSimFull ci state env args.reverse
      | letrec funs body =>
        apply evalSimulation_Letrec ci state env funs body
        intro _
        exact expsSimFull ci state { env with v := buildRecEnv funs env env.v } [body]
      | let_ name bound body =>
        apply evalSimulation_Let ci state env name bound body
        refine ⟨?_, expsSimFull ci state env [bound]⟩
        intro middle outcome values ⟨run, rfl⟩
        have clockBound := evaluateClockFull state middle env [bound] outcome run
        exact expsSimFull ci middle { env with v := nsOptBind name (headValue values) env.v } [body]
      | if_ condition yes no =>
        apply evalSimulation_If ci state env condition yes no
        refine ⟨?_, expsSimFull ci state env [condition]⟩
        intro middle outcome values branch ⟨run, rfl, chosen⟩
        have clockBound := evaluateClockFull state middle env [condition] outcome run
        rcases doIf_selected (headValue values) yes no branch chosen with equal | equal
        · subst branch; exact expsSimFull ci middle env [yes]
        · subst branch; exact expsSimFull ci middle env [no]
      | log op first second =>
        apply evalSimulation_Log ci state env op first second
        refine ⟨?_, expsSimFull ci state env [first]⟩
        intro middle outcome values selection branch ⟨run, rfl, chosen, selectionEq⟩
        subst selection
        have clockBound := evaluateClockFull state middle env [first] outcome run
        have equal := doLog_selected op (headValue values) second branch chosen
        subst branch
        exact expsSimFull ci middle env [second]
      | mat expr clauses =>
        apply evalSimulation_Mat ci state env expr clauses
        refine ⟨?_, expsSimFull ci state env [expr]⟩
        intro middle outcome values ⟨run, rfl, _⟩
        have clockBound := evaluateClockFull state middle env [expr] outcome run
        exact matchSimFull (A := A) ci middle env (headValue values) clauses bindExnV
      | handle expr clauses =>
        apply evalSimulation_Handle ci state env expr clauses
        refine ⟨?_, expsSimFull ci state env [expr]⟩
        intro middle outcome err value ⟨run, rfl, rfl, _⟩
        have clockBound := evaluateClockFull state middle env [expr] outcome run
        exact matchSimFull (A := A) ci middle env value clauses value
      | app op args =>
        apply evalSimulation_App ci state env op args
        refine ⟨?_, ?_, ?_, expsSimFull ci state env args.reverse⟩
        · intro middle outcome values pair callEnv body ⟨run, rfl, _, _, rfl, nonzero⟩
          have clockBound := evaluateClockFull state middle env args.reverse outcome run
          exact expsSimFull ci (decClock middle) callEnv [body]
        · intro middle outcome values decoded decodedResult pair evalEnv decs
            ⟨run, rfl, _, decodedRun, rfl, rfl, nonzero⟩
          have clockBound := evaluateClockFull state middle env args.reverse outcome run
          have clockEq : decoded.clock = middle.clock := by
            have hclock := congrArg (fun pair => pair.1.clock) decodedRun
            have hc := doEvalRes_clock values.reverse middle (β := Value)
            exact hclock.symm.trans hc
          exact decsSimFull (A := A) ci (decClock decoded) evalEnv decs
        · intro middle outcome values mode thunk pair callEnv body ⟨run, rfl, _, _, rfl, _, rfl, nonzero⟩
          have clockBound := evaluateClockFull state middle env args.reverse outcome run
          exact expsSimFull ci (decClock middle) callEnv [body]
termination_by (state.clock, sizeOf exprs)
decreasing_by
  all_goals try subst_vars
  all_goals simp_wf
  all_goals try simp only [listSize_reverse]
  all_goals try simp only [Prod.lex_def, decClock]
  all_goals try (have := expSize_pos second)
  all_goals try (have := listSize_pos tail)
  all_goals try dsimp only [decClock] at *
  all_goals try simp only [Nat.lt_irrefl, false_or, true_and]
  all_goals try omega

/-- Flapjack infrastructure: matching component of the mutual induction. -/
private theorem matchSimFull {Config F A : Type} [Nonempty A] (ci : CompilerInstance Config)
    (state : State F) (env : SemEnv Value) (value : Value) (clauses : List (Pat × AstHOL.Exp)) (err : Value) :
    MatchSimAt ci state env value clauses err := by
  cases clauses with
  | nil => exact evalSimulation_MatchNil ci state env value err
  | cons clause rest =>
    obtain ⟨pat, expr⟩ := clause
    apply evalSimulation_MatchCons (A := A) ci state env value pat expr rest err
    constructor
    · intro bindings _
      exact expsSimFull ci state { env with v := nsAppend (alistToNs bindings) env.v } [expr]
    · intro _
      exact matchSimFull (A := A) ci state env value rest err
termination_by (state.clock, sizeOf clauses)
decreasing_by
  all_goals simp_wf
  all_goals try simp only [Prod.lex_def]
  all_goals try (have := patSize_pos pat)
  all_goals try (have := listSize_pos rest)
  all_goals try simp only [Nat.lt_irrefl, false_or, true_and]
  all_goals try omega

/-- Flapjack infrastructure: declaration component of the mutual induction. -/
private theorem decsSimFull {Config F A : Type} [Nonempty A] (ci : CompilerInstance Config)
    (state : State F) (env : SemEnv Value) (decs : List Dec) : DecsSimAt ci state env decs := by
  cases decs with
  | nil => exact evalSimulation_DecsNil ci state env
  | cons first rest =>
    cases rest with
    | cons second tail =>
      apply evalSimulation_DecsCons ci state env first second tail
      refine ⟨?_, decsSimFull (A := A) ci state env [first]⟩
      intro middle outcome inner ⟨run, rfl⟩
      have clockBound := evaluateDecsClockFull state middle env [first] outcome run
      exact decsSimFull (A := A) ci middle (extendDecEnv inner env) (second :: tail)
    | nil =>
      cases first with
      | dtabbrev loc vars name typ => exact evalSimulation_Dtabbrev ci state env loc vars name typ
      | dexn loc name types => exact evalSimulation_Dexn ci state env loc name types
      | dtype loc types => exact evalSimulation_Dtype ci state env loc types
      | denv name => exact evalSimulation_Denv ci state env name
      | dletrec loc funs => exact evalSimulation_Dletrec ci state env loc funs
      | dmod name ds => exact evalSimulation_Dmod ci state env name ds (decsSimFull (A := A) ci state env ds)
      | dlet loc pat expr =>
        apply evalSimulation_Dlet (A := A) ci state env loc pat expr
        intro _
        exact expsSimFull ci state env [expr]
      | dlocal locals body =>
        apply evalSimulation_Dlocal ci state env locals body
        refine ⟨?_, decsSimFull (A := A) ci state env locals⟩
        intro middle outcome inner ⟨run, rfl⟩
        have clockBound := evaluateDecsClockFull state middle env locals outcome run
        exact decsSimFull (A := A) ci middle (extendDecEnv inner env) body
termination_by (state.clock, sizeOf decs)
decreasing_by
  all_goals try subst_vars
  all_goals simp_wf
  all_goals try simp only [Prod.lex_def]
  all_goals try (have := decSize_pos second)
  all_goals try (have := listSize_pos tail)
  all_goals try (have := patSize_pos pat)
  all_goals try simp only [Nat.lt_irrefl, false_or, true_and]
  all_goals try omega
end

/-- The full source evaluator simulation, including the independent inhabited
unused HOL expression binder. The evaluator inherits the rational-cut real
number assumption. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem eval_simulation {Config F A : Type} [Nonempty A] (ci : CompilerInstance Config) :
    (∀ (s : State F) (env : SemEnv Value) (exps : List AstHOL.Exp)
      (s' : State F) (res : Result (List Value) Value) (_es : A) (t : State F) (env' : SemEnv Value),
      evaluate s env exps = (s', res) ∧ stateRel ci s t ∧
        envRel (ValueRel (oracleState t.evalState)) env env' ∧ res ≠ .err (.abort .typeError) →
      ∃ es' t' res', evaluate t env' exps = (t', res') ∧ stateRel ci s' t' ∧
        es' = oracleState t'.evalState ∧ resultRel (List.Forall₂ (ValueRel es')) (ValueRel es') res res' ∧
        envStoreForward (oracleState t.evalState) es' ∧
        (¬ abort res' → envStackForward (oracleState t.evalState) es')) ∧
    (∀ (s : State F) (env : SemEnv Value) (x : Value) (rows : List (Pat × AstHOL.Exp)) (errX : Value)
      (s' : State F) (res : Result (List Value) Value) (es : EvalOracleState) (t : State F)
      (env' : SemEnv Value) (y errY : Value),
      evaluateMatch s env x rows errX = (s', res) ∧ stateRel ci s t ∧ es = oracleState t.evalState ∧
        envRel (ValueRel es) env env' ∧ ValueRel es x y ∧ ValueRel es errX errY ∧
        res ≠ .err (.abort .typeError) →
      ∃ es' t' res', evaluateMatch t env' y rows errY = (t', res') ∧ stateRel ci s' t' ∧
        es' = oracleState t'.evalState ∧ resultRel (List.Forall₂ (ValueRel es')) (ValueRel es') res res' ∧
        envStoreForward es es' ∧ (¬ abort res' → envStackForward es es')) ∧
    (∀ (s : State F) (env : SemEnv Value) (decs : List Dec) (s' : State F)
      (res : Result (SemEnv Value) Value) (t : State F) (env' : SemEnv Value),
      evaluateDecs s env decs = (s', res) ∧ stateRel ci s t ∧
        envRel (ValueRel (oracleState t.evalState)) env env' ∧ res ≠ .err (.abort .typeError) →
      ∃ es' t' res', evaluateDecs t env' decs = (t', res') ∧ stateRel ci s' t' ∧
        es' = oracleState t'.evalState ∧ resultRel (envRel (ValueRel es')) (ValueRel es') res res' ∧
        envStoreForward (oracleState t.evalState) es' ∧
        (¬ abort res' → envStackForward (oracleState t.evalState) es')) := by
  exact ⟨fun s env exps => expsSimFull (A := A) ci s env exps,
    fun s env x rows errX => matchSimFull (A := A) ci s env x rows errX,
    fun s env decs => decsSimFull (A := A) ci s env decs⟩
end Flapjack.Compiler.Backend.SourceEval.Proofs
