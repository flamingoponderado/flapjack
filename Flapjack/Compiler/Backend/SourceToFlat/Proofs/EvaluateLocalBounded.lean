module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalEnvironment
public import Flapjack.EvaluateHOL.ClockFull

@[expose] public section

/-! Clock-bounded local expression and list simulation infrastructure. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

private theorem flatEvaluate_cons {C F : Type} (flat : FlatSem.State C F)
    (flatEnv : FlatSem.Environment FlatSem.Value) (trace : List VarN)
    (compMap : Environment) (first second : AstHOL.Exp) (rest : List AstHOL.Exp) :
    FlatSem.evaluate flatEnv flat (compileExps trace compMap (first :: second :: rest)) =
      let head := FlatSem.evaluate flatEnv flat [compileExp trace compMap first]
      match head.2 with
      | .err error => (head.1, .err error)
      | .val values =>
        let tail := FlatSem.evaluate flatEnv head.1 (compileExps trace compMap (second :: rest))
        match tail.2 with
        | .err error => (tail.1, .err error)
        | .val values' => (tail.1, .val (@Flapjack.holHd FlatSem.Value ⟨FlatSem.unitValue⟩ values :: values')) := by
  simp only [compileExps]
  rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
    [compileExp trace compMap first] (FlatLang.Exp.lit .none (.intLit 0)) []).1]
  rfl

/-- Compose local expression induction hypotheses over an arbitrary list. -/
theorem boundedEnvListStep_of_each {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (limit : Nat) (expressions : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ expressions → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    ∀ (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
      (source : State F) (flat : FlatSem.State C F) (baseEnv : SemEnv Value)
      (sourceLocal : Namespace ModN VarN Value) (flatEnv : FlatSem.Environment FlatSem.Value)
      (traces : List BackendCommon.Tra) (trace : List VarN) (baseMap : Environment) (gen : EnvironmentGenerationStore),
      source.clock ≤ limit →
      EnvRel genv sourceLocal flatEnv.v →
      GlobalEnvInv genv baseMap (fun n => n ∈ flatEnv.v.map Prod.fst) baseEnv →
      traces.length = flatEnv.v.length →
      factoredInvariant interp transform gen genv (start, finish, other) source flat →
      envGenRel gen source.evalState →
      (∀ last, EvaluateHOL.evaluate source { baseEnv with v := nsAppend sourceLocal baseEnv.v } expressions ≠
        (last, .err (.abort .typeError))) →
      LocalExpressionListStep interp transform genv start finish other source flat
        { baseEnv with v := nsAppend sourceLocal baseEnv.v } flatEnv trace
        { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v } gen expressions := by
  induction expressions with
  | nil =>
    intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen _ _ _ _ invariant generation _
    refine ⟨genv, ?_, ?_⟩
    · simp only [ExprListSim, EvaluateHOL.evaluate, compileExps, FlatSem.evaluate]
      exact ⟨.value .nil, invariant.2.2.1⟩
    · simp only [EvaluateHOL.evaluate, compileExps, FlatSem.evaluate]
      exact ⟨GlobalGrowth.refl genv, invariant, generation, oracForwardRel_refl interp source.evalState⟩
  | cons first rest ih =>
    intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
    let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
    let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
    cases rest with
    | nil =>
      have step := each first (by simp) genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen
        clockBound localRel envInv tracesLen invariant generation safe
      change LocalExpressionStep interp transform genv start finish other source flat sourceEnv flatEnv trace compMap gen first at step
      change LocalExpressionListStep interp transform genv start finish other source flat sourceEnv flatEnv trace compMap gen [first]
      obtain ⟨nextGenv, sim, post⟩ := step
      refine ⟨nextGenv, by simpa [ExprSim, ExprListSim, compileExps] using sim, ?_⟩
      cases result : (EvaluateHOL.evaluate source sourceEnv [first]).2 with
      | val value => simpa only [result, compileExps] using post
      | err error =>
        cases error with
        | abort error => simp
        | raise value => simpa only [result, compileExps] using post
    | cons second tail =>
      have headSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [first] ≠ (last, .err (.abort .typeError)) := by
        intro last bad
        apply safe last
        change EvaluateHOL.evaluate source sourceEnv (first :: second :: tail) = _
        simp only [sourceEvaluate_cons, bad]
      have headStep := each first (by simp) genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen
        clockBound localRel envInv tracesLen invariant generation headSafe
      change LocalExpressionListStep interp transform genv start finish other source flat sourceEnv flatEnv trace
        compMap gen (first :: second :: tail)
      obtain ⟨middleGenv, headSim, headPost⟩ := headStep
      unfold ExprSim at headSim
      generalize sourceHead : EvaluateHOL.evaluate source sourceEnv [first] = sourceHeadResult at headSim headPost
      obtain ⟨middleSource, sourceHeadResult⟩ := sourceHeadResult
      generalize flatHead : FlatSem.evaluate flatEnv flat [compileExp trace compMap first] = flatHeadResult at headSim headPost
      obtain ⟨middleFlat, flatHeadResult⟩ := flatHeadResult
      obtain ⟨headRelated, headStates⟩ := headSim
      cases headRelated with
      | abort error =>
        refine ⟨middleGenv, ?_, ?_⟩
        · unfold ExprListSim
          rw [sourceEvaluate_cons, sourceHead, flatEvaluate_cons, flatHead]
          exact ⟨.abort error, headStates⟩
        · rw [sourceEvaluate_cons, sourceHead]
          trivial
      | raise headValue =>
        refine ⟨middleGenv, ?_, ?_⟩
        · unfold ExprListSim
          rw [sourceEvaluate_cons, sourceHead, flatEvaluate_cons, flatHead]
          exact ⟨.raise headValue, headStates⟩
        · rw [sourceEvaluate_cons, sourceHead, flatEvaluate_cons, flatHead]
          exact headPost
      | @value sourceValues flatValues headValues =>
        obtain ⟨sourceValue, sourceEq⟩ := EvaluateProps.evaluateSingFull source sourceEnv first middleSource sourceValues sourceHead
        subst sourceValues
        cases headValues with
        | cons headValue tailValues =>
          cases tailValues with
          | nil =>
            obtain ⟨headGrowth, middleInvariant, middleGeneration, headForward⟩ := headPost
            have tailStep : LocalExpressionListStep interp transform middleGenv start finish other middleSource middleFlat
                sourceEnv flatEnv trace compMap gen (second :: tail) := by
              have tailSafe : ∀ last, EvaluateHOL.evaluate middleSource sourceEnv (second :: tail) ≠
                  (last, .err (.abort .typeError)) := by
                intro last bad
                apply safe last
                change EvaluateHOL.evaluate source sourceEnv (first :: second :: tail) = _
                simp only [sourceEvaluate_cons, sourceHead, bad]
              apply ih
              · intro expr member
                exact each expr (List.mem_cons_of_mem _ member)
              · exact Nat.le_trans (EvaluateHOL.evaluateClockFull source middleSource sourceEnv [first] _ sourceHead) clockBound
              · exact envRel_growth genv middleGenv headGrowth sourceLocal flatEnv.v localRel
              · exact globalEnvInv_growth genv middleGenv headGrowth baseMap (fun n => n ∈ flatEnv.v.map Prod.fst) baseEnv envInv
              · exact tracesLen
              · exact middleInvariant
              · exact middleGeneration
              · exact tailSafe
            obtain ⟨finalGenv, tailSim, tailPost⟩ := tailStep
            unfold ExprListSim at tailSim
            generalize sourceTail : EvaluateHOL.evaluate middleSource sourceEnv (second :: tail) = sourceTailResult at tailSim tailPost
            obtain ⟨finalSource, sourceTailResult⟩ := sourceTailResult
            generalize flatTail : FlatSem.evaluate flatEnv middleFlat (compileExps trace compMap (second :: tail)) = flatTailResult at tailSim tailPost
            obtain ⟨finalFlat, flatTailResult⟩ := flatTailResult
            obtain ⟨tailRelated, tailStates⟩ := tailSim
            cases tailRelated with
            | abort error =>
              refine ⟨finalGenv, ?_, ?_⟩
              · unfold ExprListSim
                simp only [sourceEvaluate_cons, sourceHead, flatEvaluate_cons, flatHead, sourceTail, flatTail]
                exact ⟨.abort error, tailStates⟩
              · simp only [sourceEvaluate_cons, sourceHead, sourceTail]
            | raise tailValue =>
              obtain ⟨tailGrowth, finalInvariant, finalGeneration, tailForward⟩ := tailPost
              refine ⟨finalGenv, ?_, ?_⟩
              · unfold ExprListSim
                simp only [sourceEvaluate_cons, sourceHead, flatEvaluate_cons, flatHead, sourceTail, flatTail]
                exact ⟨.raise tailValue, tailStates⟩
              · simp only [sourceEvaluate_cons, sourceHead, flatEvaluate_cons, flatHead, sourceTail, flatTail]
                exact ⟨headGrowth.trans tailGrowth, finalInvariant, finalGeneration,
                  oracForwardRel_trans interp _ _ _ ⟨headForward, tailForward⟩⟩
            | value tailValues =>
              obtain ⟨tailGrowth, finalInvariant, finalGeneration, tailForward⟩ := tailPost
              refine ⟨finalGenv, ?_, ?_⟩
              · unfold ExprListSim
                simp only [sourceEvaluate_cons, sourceHead, flatEvaluate_cons, flatHead, sourceTail, flatTail]
                simp only [EvaluateHOL.headValue, Flapjack.holHd]
                exact ⟨.value (.cons (valueRel_growth middleGenv finalGenv tailGrowth _ _ headValue) tailValues), tailStates⟩
              · simp only [sourceEvaluate_cons, sourceHead, flatEvaluate_cons, flatHead, sourceTail, flatTail]
                exact ⟨headGrowth.trans tailGrowth, finalInvariant, finalGeneration,
                  oracForwardRel_trans interp _ _ _ ⟨headForward, tailForward⟩⟩



/-- A bounded initializer simulation supplies the bounded value-declaration
case, including arbitrary patterns and source-safe error behavior. -/
theorem factoredDecBoundedIH_dlet_expression {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp)
    (expressionIH : LocalEnvBoundedIH (F := F) interp transform limit expr) :
    FactoredDecBoundedIH (F := F) interp transform limit [.dlet location pattern expr] := by
  intro genv env nextEnv sourceEnv trace source sourceLast flat start finish next other n n' gen nextGen
    flatDecs result clockBound sourceRun invariant compiled envInv notTypeError generation future bounded
  have safe : ∀ last, EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply notTypeError
    exact congrArg Prod.snd (sourceRun.symm.trans bad)
  have expressionSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [expr] ≠
      (last, .err (.abort .typeError)) := by
    obtain ⟨distinct, wellformed⟩ := dlet_conditions_of_safe source sourceEnv location pattern expr safe
    intro last bad
    apply safe last
    simp [EvaluateHOL.evaluateDecs, distinct, wellformed, bad]
  have sourceEq : { sourceEnv with v := nsAppend nsEmpty sourceEnv.v } = sourceEnv := by
    simp only [(nsAppend_nsEmpty sourceEnv.v).2]
  have mapEq : { env with v := bindLocals [] [] env.v } = env := by
    simp [bindLocals, nsBindList]
  have step := expressionIH genv start finish other source flat sourceEnv nsEmpty ⟨[]⟩ []
    ((AstHOL.patBindings pattern).reverse ++ trace) env gen clockBound (.empty genv)
    (by simpa using envInv) rfl invariant generation (by simpa only [sourceEq] using expressionSafe)
  have expressionStep : DletExpressionStep interp transform genv start finish other source flat sourceEnv
      ((AstHOL.patBindings pattern).reverse ++ trace) env gen expr := by
    change LocalExpressionStep interp transform genv start finish other source flat sourceEnv ⟨[]⟩
      ((AstHOL.patBindings pattern).reverse ++ trace) env gen expr
    simpa only [List.map_nil, sourceEq, mapEq] using step
  exact evaluateDlet_case_factored interp transform genv start finish next other source sourceLast flat sourceEnv
    trace n n' env nextEnv gen nextGen location pattern expr flatDecs result
    sourceRun invariant compiled envInv notTypeError generation future bounded expressionStep

end Flapjack.Compiler.Backend.SourceToFlat
