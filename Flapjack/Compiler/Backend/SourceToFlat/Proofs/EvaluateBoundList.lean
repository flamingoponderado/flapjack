module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateGrowingNamedLet
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateControl
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.MemoryOps
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.Equality
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PrimitiveTest

@[expose] public section

/-! Growing argument lists in local environments using the reviewed relations. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- Abort-sensitive growing simulation for a local expression list. -/
def LocalExpressionListStep {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (flatEnv : FlatSem.Environment FlatSem.Value) (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore) (args : List AstHOL.Exp) : Prop :=
  let sourceResult := EvaluateHOL.evaluate source sourceEnv args
  let flatResult := FlatSem.evaluate flatEnv flat (compileExps trace compMap args)
  ∃ nextGenv, ExprListSim nextGenv compMap trace sourceEnv flatEnv source flat args ∧
    match sourceResult.2 with
    | .err (.abort _) => True
    | _ => GlobalGrowth genv nextGenv ∧
        factoredInvariant interp transform gen nextGenv (start, finish, other) sourceResult.1 flatResult.1 ∧
        envGenRel gen sourceResult.1.evalState ∧ oracForwardRel interp source.evalState sourceResult.1.evalState

/-- A singleton expression step supplies the corresponding list step. -/
theorem localExpressionListStep_singleton {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (flatEnv : FlatSem.Environment FlatSem.Value) (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore) (expr : AstHOL.Exp)
    (step : LocalExpressionStep interp transform genv start finish other source flat sourceEnv flatEnv trace compMap gen expr) :
    LocalExpressionListStep interp transform genv start finish other source flat sourceEnv flatEnv trace compMap gen [expr] := by
  obtain ⟨nextGenv, sim, post⟩ := step
  refine ⟨nextGenv, by simpa [ExprSim, ExprListSim, compileExps] using sim, ?_⟩
  cases result : (EvaluateHOL.evaluate source sourceEnv [expr]).2 with
  | val value => simpa only [result, compileExps] using post
  | err error =>
    cases error with
    | abort error => simp
    | raise value => simpa only [result, compileExps] using post

/-- The empty local argument list leaves both states unchanged. -/
theorem localExpressionListStep_empty {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (flatEnv : FlatSem.Environment FlatSem.Value) (trace : List VarN) (compMap : Environment)
    (gen : EnvironmentGenerationStore)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState) :
    LocalExpressionListStep interp transform genv start finish other source flat sourceEnv flatEnv trace compMap gen [] := by
  refine ⟨genv, ?_, ?_⟩
  · simp only [ExprListSim, EvaluateHOL.evaluate, compileExps, FlatSem.evaluate]
    exact ⟨.value .nil, invariant.2.2.1⟩
  · simp only [EvaluateHOL.evaluate, compileExps, FlatSem.evaluate]
    exact ⟨GlobalGrowth.refl genv, invariant, generation, oracForwardRel_refl interp source.evalState⟩

/-- Unfold the source evaluator on two or more expressions for simulation.
This convenience equation has no separate HOL declaration. -/
theorem sourceEvaluate_cons {F : Type} (source : State F) (env : SemEnv Value)
    (first second : AstHOL.Exp) (rest : List AstHOL.Exp) :
    EvaluateHOL.evaluate source env (first :: second :: rest) =
      let head := EvaluateHOL.evaluate source env [first]
      match head.2 with
      | .err error => (head.1, .err error)
      | .val values =>
        let tail := EvaluateHOL.evaluate head.1 env (second :: rest)
        match tail.2 with
        | .err error => (tail.1, .err error)
        | .val values' => (tail.1, .val (EvaluateHOL.headValue values :: values')) := by
  rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source env [first] []).1]
  rfl

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

/-- Sequential composition of a growing expression step and the growing
induction hypothesis for a nonempty tail. -/
theorem localExpressionListStep_cons {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (flatEnv : FlatSem.Environment FlatSem.Value) (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (first second : AstHOL.Exp) (rest : List AstHOL.Exp)
    (headStep : LocalExpressionStep interp transform genv start finish other source flat sourceEnv flatEnv trace compMap gen first)
    (tailIH : ∀ (middleGenv : GlobalEnv) (middleSource : State F) (middleFlat : FlatSem.State C F)
      (headValue : Value), EvaluateHOL.evaluate source sourceEnv [first] = (middleSource, .val [headValue]) →
      GlobalGrowth genv middleGenv →
      factoredInvariant interp transform gen middleGenv (start, finish, other) middleSource middleFlat →
      envGenRel gen middleSource.evalState →
      LocalExpressionListStep interp transform middleGenv start finish other middleSource middleFlat
        sourceEnv flatEnv trace compMap gen (second :: rest)) :
    LocalExpressionListStep interp transform genv start finish other source flat sourceEnv flatEnv trace compMap gen
      (first :: second :: rest) := by
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
        obtain ⟨finalGenv, tailSim, tailPost⟩ := tailIH middleGenv middleSource middleFlat sourceValue sourceHead headGrowth
          middleInvariant middleGeneration
        unfold ExprListSim at tailSim
        generalize sourceTail : EvaluateHOL.evaluate middleSource sourceEnv (second :: rest) = sourceTailResult at tailSim tailPost
        obtain ⟨finalSource, sourceTailResult⟩ := sourceTailResult
        generalize flatTail : FlatSem.evaluate flatEnv middleFlat (compileExps trace compMap (second :: rest)) = flatTailResult at tailSim tailPost
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


end Flapjack.Compiler.Backend.SourceToFlat
