import Flapjack.Compiler.Backend.FlatPattern.Proofs.ClockedApplication
import Flapjack.Compiler.Backend.FlatPattern.Proofs.ClockedDeclaration

/-! Induction on the proof-side evaluator's clock and expression weight.
The evaluator and relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.Basis.Pure.MlString (ofString)

/-- Expression simulation remains valid under a smaller clock bound. -/
theorem expressionSimulationUpTo_mono {C F : Type} (cfg stateCfg : Config) (large small : Nat)
    (expression : FlatLang.Exp) (sim : ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg large expression)
    (bound : small ≤ large) : ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg small expression := by
  intro sourceEnv targetEnv source target sourceFinal result n sourceBound run envs states nameBound safe
  exact sim sourceEnv targetEnv source target sourceFinal result n (by omega) run envs states nameBound safe

/-- Each list member has less weight than its containing expression list. -/
theorem expressionWeight_member (expression : FlatLang.Exp) (expressions : List FlatLang.Exp)
    (member : expression ∈ expressions) : FlatSem.expWeight expression < FlatSem.expsWeight expressions := by
  induction expressions with
  | nil => simp at member
  | cons head tail ih =>
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · simp only [FlatSem.expsWeight]; omega
    · have bound := ih member
      simp only [FlatSem.expsWeight]
      omega

/-- Each pattern-row body has less weight than its containing row list. -/
theorem rowWeight_member (pattern : FlatLang.Pat) (body : FlatLang.Exp)
    (rows : List (FlatLang.Pat × FlatLang.Exp)) (member : (pattern, body) ∈ rows) :
    FlatSem.expWeight body < FlatSem.rowsWeight rows := by
  induction rows with
  | nil => simp at member
  | cons row tail ih =>
    obtain ⟨p, e⟩ := row
    simp only [List.mem_cons, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩ | member
    · simp only [FlatSem.rowsWeight]; omega
    · have bound := ih member
      simp only [FlatSem.rowsWeight]
      omega

/-- The proof-side flat pattern compiler simulates expression evaluation at
every clock. Its evaluator and relations still require HOL correspondence
review before this can be tagged as the original correctness theorem. -/
theorem expressionSimulationUpTo_all {C F : Type} (clock : Nat) :
    ∀ (cfg stateCfg : Config) (expression : FlatLang.Exp),
      ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock expression := by
  induction clock using Nat.strongRecOn with
  | ind clock clockIH =>
    have allWeights : ∀ weight (cfg stateCfg : Config) (expression : FlatLang.Exp),
        FlatSem.expWeight expression = weight → ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock expression := by
      intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        intro cfg stateCfg expression weightEq
        cases expression with
        | lit trace literal =>
          exact expressionSimulation_upTo cfg stateCfg clock _ (compile_lit_simulation cfg stateCfg trace literal)
        | varLocal trace name =>
          exact expressionSimulation_upTo cfg stateCfg clock _ (compile_var_simulation cfg stateCfg trace name)
        | fn trace name body =>
          exact expressionSimulation_upTo cfg stateCfg clock _ (compile_fn_simulation cfg stateCfg trace name body)
        | raise trace body =>
          apply compile_raise_simulation_upTo cfg stateCfg clock trace body
          apply weightIH (FlatSem.expWeight body) (by simp [FlatSem.expWeight] at weightEq; omega) cfg stateCfg body rfl
        | let_ trace name first body =>
          apply compile_let_simulation_upTo cfg stateCfg clock trace name first body
          · apply weightIH (FlatSem.expWeight first) (by simp [FlatSem.expWeight] at weightEq; omega) cfg stateCfg first rfl
          · apply weightIH (FlatSem.expWeight body) (by simp [FlatSem.expWeight] at weightEq; omega) cfg stateCfg body rfl
        | letrec trace funs body =>
          apply compile_letrec_simulation_upTo cfg stateCfg clock trace funs body
          apply weightIH (FlatSem.expWeight body) (by simp [FlatSem.expWeight] at weightEq; omega) cfg stateCfg body rfl
        | if_ trace cond yes no =>
          apply compile_if_simulation_upTo cfg stateCfg clock trace cond yes no
          · apply weightIH (FlatSem.expWeight cond) (by simp [FlatSem.expWeight] at weightEq; omega) cfg stateCfg cond rfl
          · apply weightIH (FlatSem.expWeight yes) (by simp [FlatSem.expWeight] at weightEq; omega) cfg stateCfg yes rfl
          · apply weightIH (FlatSem.expWeight no) (by simp [FlatSem.expWeight] at weightEq; omega) cfg stateCfg no rfl
        | con trace tag args =>
          apply compile_con_simulation_upTo cfg stateCfg clock trace tag args
          intro expression member
          have h := expressionWeight_member expression args member
          apply weightIH (FlatSem.expWeight expression) (by simp [FlatSem.expWeight] at weightEq; omega) cfg stateCfg expression rfl
        | mat trace scrutinee rows =>
          apply compile_mat_simulation_upTo cfg stateCfg clock trace scrutinee rows
          · apply weightIH (FlatSem.expWeight scrutinee) (by simp [FlatSem.expWeight] at weightEq; omega) cfg stateCfg scrutinee rfl
          · intro pattern body member
            have h := rowWeight_member pattern body rows member
            apply weightIH (FlatSem.expWeight body) (by simp [FlatSem.expWeight] at weightEq; omega) cfg stateCfg body rfl
        | handle trace protectedExpr rows =>
          apply compile_handle_simulation_upTo cfg stateCfg clock trace protectedExpr rows
          · apply weightIH (FlatSem.expWeight protectedExpr) (by simp [FlatSem.expWeight] at weightEq; omega) cfg stateCfg protectedExpr rfl
          · intro pattern body member
            have h := rowWeight_member pattern body rows member
            apply weightIH (FlatSem.expWeight body) (by simp [FlatSem.expWeight] at weightEq; omega) cfg stateCfg body rfl
        | app trace op args =>
          have argsIH : ∀ expression ∈ args, ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock expression := by
            intro expression member
            have h := expressionWeight_member expression args member
            apply weightIH (FlatSem.expWeight expression) ?_ cfg stateCfg expression rfl
            simp only [FlatSem.expWeight] at weightEq
            omega
          cases op with
          | src sourceOp =>
            by_cases isCall : sourceOp = .opapp
            · subst sourceOp
              intro sourceEnv targetEnv source target sourceFinal sourceResult n clockBound run envs states bound safe
              have argsAtClock : ∀ expression ∈ args, ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg source.clock expression := by
                intro expression member
                exact expressionSimulationUpTo_mono cfg stateCfg clock source.clock expression (argsIH expression member) clockBound
              apply compile_call_simulation_at_clock_boundedArgs cfg stateCfg trace args source.clock argsAtClock ?_
                sourceEnv targetEnv source target sourceFinal sourceResult n rfl run envs states bound safe
              intro bodyCfg body bodySourceEnv bodyTargetEnv bodySource bodyTarget bodyFinal bodyResult bodyN smaller bodyRun bodyEnvs bodyStates bodyBound bodySafe
              have bodySim := clockIH bodySource.clock (by omega) bodyCfg stateCfg body
              exact bodySim bodySourceEnv bodyTargetEnv bodySource bodyTarget bodyFinal bodyResult bodyN (by omega)
                bodyRun bodyEnvs bodyStates bodyBound bodySafe
            · by_cases isEval : sourceOp = .eval
              · subst sourceOp
                intro sourceEnv targetEnv source target sourceFinal sourceResult n clockBound run envs states bound safe
                have argsAtClock : ∀ expression ∈ args, ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg source.clock expression := by
                  intro expression member
                  exact expressionSimulationUpTo_mono cfg stateCfg clock source.clock expression (argsIH expression member) clockBound
                apply compile_eval_simulation_at_clock_boundedArgs cfg stateCfg trace args source.clock argsAtClock ?_
                  sourceEnv targetEnv source target sourceFinal sourceResult n rfl run envs states bound safe
                intro decSource decTarget decFinal declarations outcome smaller decRun decStates decSafe
                have members : ∀ declaration ∈ declarations,
                    ExpressionSimulationUpTo (C := C) (F := F) stateCfg stateCfg decSource.clock declaration := by
                  intro declaration _
                  exact clockIH decSource.clock (by omega) stateCfg stateCfg declaration
                exact evaluateDecs_simulation_upTo stateCfg stateCfg decSource.clock declarations members
                  decSource decTarget decFinal outcome (by omega) decStates decRun decSafe
              · by_cases isForce : sourceOp = .thunkOp .forceThunk
                · subst sourceOp
                  have smallerBody := FlatSem.appUnit_force_weight trace args
                  have generatedIH := weightIH (FlatSem.expWeight (FlatSem.appUnit (.varLocal .none (ofString "f"))))
                    (by omega) cfg stateCfg
                    (FlatSem.appUnit (.varLocal .none (ofString "f"))) rfl
                  intro sourceEnv targetEnv source target sourceFinal sourceResult n clockBound run envs states bound safe
                  have argsAtClock : ∀ expression ∈ args, ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg source.clock expression := by
                    intro expression member
                    exact expressionSimulationUpTo_mono cfg stateCfg clock source.clock expression (argsIH expression member) clockBound
                  apply compile_force_simulation_at_clock_boundedArgs cfg stateCfg trace args source.clock argsAtClock ?_
                    sourceEnv targetEnv source target sourceFinal sourceResult n rfl run envs states bound safe
                  intro bodySourceEnv bodyTargetEnv bodySource bodyTarget bodyFinal bodyResult bodyN bodyClock bodyRun bodyEnvs bodyStates bodyBound bodySafe
                  exact generatedIH bodySourceEnv bodyTargetEnv bodySource bodyTarget bodyFinal bodyResult bodyN (by omega)
                    bodyRun bodyEnvs bodyStates bodyBound bodySafe
                · exact compile_nonrecursiveSourceApp_simulation_upTo cfg stateCfg trace sourceOp args clock isCall isEval isForce argsIH
          | globalVarAlloc count => exact compile_flatApp_simulation_upTo cfg stateCfg trace (.globalVarAlloc count) args clock (by intro _; simp) argsIH
          | globalVarInit index => exact compile_flatApp_simulation_upTo cfg stateCfg trace (.globalVarInit index) args clock (by intro _; simp) argsIH
          | globalVarLookup index => exact compile_flatApp_simulation_upTo cfg stateCfg trace (.globalVarLookup index) args clock (by intro _; simp) argsIH
          | tagLenEq tag length => exact compile_flatApp_simulation_upTo cfg stateCfg trace (.tagLenEq tag length) args clock (by intro _; simp) argsIH
          | lenEq length => exact compile_flatApp_simulation_upTo cfg stateCfg trace (.lenEq length) args clock (by intro _; simp) argsIH
          | el index => exact compile_flatApp_simulation_upTo cfg stateCfg trace (.el index) args clock (by intro _; simp) argsIH
          | id => exact compile_flatApp_simulation_upTo cfg stateCfg trace .id args clock (by intro _; simp) argsIH
    intro cfg stateCfg expression
    exact allWeights (FlatSem.expWeight expression) cfg stateCfg expression rfl

/-- Every expression satisfies the proof-side forward simulation without a
fixed external clock bound. -/
theorem expressionSimulation_all {C F : Type} (cfg stateCfg : Config) (expression : FlatLang.Exp) :
    ExpressionSimulation (C := C) (F := F) cfg stateCfg expression := by
  intro sourceEnv targetEnv source target sourceFinal sourceResult n run envs states bound safe
  exact expressionSimulationUpTo_all source.clock cfg stateCfg expression
    sourceEnv targetEnv source target sourceFinal sourceResult n (by omega) run envs states bound safe

/-- Every expression list satisfies the corresponding proof-side simulation. -/
theorem expressionsSimulation_all {C F : Type} (cfg stateCfg : Config) (expressions : List FlatLang.Exp) :
    ExpressionsSimulation (C := C) (F := F) cfg stateCfg expressions :=
  compileExps_simulation cfg stateCfg expressions (by intro expression _; exact expressionSimulation_all cfg stateCfg expression)

/-- Compiled declaration lists preserve related states and non-type-error
outcomes in the current proof-side evaluator. -/
theorem evaluateDecs_simulation_all {C F : Type} (cfg stateCfg : Config)
    (source target sourceFinal : FlatSem.State C F) (declarations : List FlatLang.Exp)
    (outcome : Option (SemanticPrimitivesHOL.ErrorResult FlatSem.Value))
    (states : StateRel stateCfg source target) (run : FlatSem.evaluateDecs source declarations = (sourceFinal, outcome))
    (safe : outcome ≠ some (.abort .typeError)) :
    ∃ targetFinal targetOutcome,
      FlatSem.evaluateDecs target (declarations.map (compileDec cfg)) = (targetFinal, targetOutcome) ∧
      StateRel stateCfg sourceFinal targetFinal ∧ optionRel FlatErrorRel outcome targetOutcome :=
  evaluateDecs_simulation cfg stateCfg declarations (by intro declaration _; exact expressionSimulation_all cfg stateCfg declaration)
    source target sourceFinal outcome states run safe

/-- The expression-list and declaration-list simulations in a single
conjunction. This is proof-side infrastructure: `FlatSem.evaluate`, `ValueRel`,
`EnvRel`, and `StateRel` have not yet completed HOL correspondence review, so
this is not tagged as the original theorem. -/
theorem compileExps_evaluate_proofSide {C F : Type} (stateCfg : Config) :
    (∀ (env1 : FlatSem.Environment FlatSem.Value) (s1 : FlatSem.State C F)
      (xs : List FlatLang.Exp) (t1 : FlatSem.State C F)
      (r1 : SemanticPrimitivesHOL.Result (List FlatSem.Value) FlatSem.Value)
      (i : Nat) (sg : Bool) (ys : List FlatLang.Exp) (n : Nat)
      (env2 : FlatSem.Environment FlatSem.Value) (s2 : FlatSem.State C F) (cfg : Config),
      FlatSem.evaluate env1 s1 xs = (t1, r1) → compileExps cfg xs = (i, sg, ys) →
      EnvRel n env1 env2 → StateRel stateCfg s1 s2 → i < n → r1 ≠ .err (.abort .typeError) →
      ∃ t2 r2, FlatResultRel r1 r2 ∧ StateRel stateCfg t1 t2 ∧ FlatSem.evaluate env2 s2 ys = (t2, r2)) ∧
    (∀ (s1 : FlatSem.State C F) (decs : List FlatLang.Exp) (s2 t1 : FlatSem.State C F)
      (cfg : Config) (decs' : List FlatLang.Exp) (res : Option (SemanticPrimitivesHOL.ErrorResult FlatSem.Value)),
      FlatSem.evaluateDecs s1 decs = (t1, res) → decs' = decs.map (compileDec cfg) →
      StateRel stateCfg s1 s2 → res ≠ some (.abort .typeError) →
      ∃ t2 res', FlatSem.evaluateDecs s2 decs' = (t2, res') ∧ optionRel FlatErrorRel res res' ∧ StateRel stateCfg t1 t2) := by
  constructor
  · intro env1 s1 xs t1 r1 i sg ys n env2 s2 cfg run compiled envs states bound safe
    have compiledBound : (compileExps cfg xs).1 < n := by simpa [compiled] using bound
    obtain ⟨t2, r2, targetRun, finalStates, results⟩ := expressionsSimulation_all cfg stateCfg xs
      env1 env2 s1 s2 t1 r1 n run envs states compiledBound safe
    exact ⟨t2, r2, results, finalStates, by simpa [compiled] using targetRun⟩
  · intro s1 decs s2 t1 cfg decs' res run compiled states safe
    subst decs'
    obtain ⟨t2, res', targetRun, finalStates, outcomes⟩ :=
      evaluateDecs_simulation_all cfg stateCfg s1 s2 t1 decs res states run safe
    exact ⟨t2, res', targetRun, outcomes, finalStates⟩

end Flapjack.Compiler.Backend.FlatPattern
