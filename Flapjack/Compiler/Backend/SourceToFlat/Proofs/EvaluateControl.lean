module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateCases
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvalOracleSimulation
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.FiniteMapGrowth
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PrimitiveType
public import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateClock
public import Flapjack.EvaluateHOL.ClockFull
public import Flapjack.EvaluateProps.Length

@[expose] public section

/-! Composition of expression simulations over the source-to-flat relations.
The expression simulations remain untagged pending evaluator review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL

namespace ResultRelPort

/-- Roundtrip for the global carrier's canonical finite maps. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env :=
  GlobalEnv.holFmapAsFiniteSupportWitness env

end ResultRelPort

/-- Relate successful results using an arbitrary payload relation, raised
exceptions using the value relation, and identical aborts. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "result_rel"
  (fmap_as_finite_support := [c, tys])]
inductive ResultRel {α β : Type} (payload : GlobalEnv → α → β → Prop) (genv : GlobalEnv) :
    Result α SemanticPrimitivesHOL.Value → Result β FlatSem.Value → Prop where
  | value {source flat} (related : payload genv source flat) : ResultRel payload genv (.val source) (.val flat)
  | raise {source flat} (related : ValueRel genv source flat) :
      ResultRel payload genv (.err (.raise source)) (.err (.raise flat))
  | abort (error : Abort) : ResultRel payload genv (.err (.abort error)) (.err (.abort error))

/-- The complete case equations for the result relation. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "result_rel_eqns"
  (fmap_as_finite_support := [c, tys])]
theorem resultRel_eqns {α β γ : Type} [Nonempty γ] (payload : GlobalEnv → α → β → Prop) :
    (∀ genv (value : α) (result : Result β FlatSem.Value),
      ResultRel payload genv (.val value) result ↔
        ∃ value', payload genv value value' ∧ result = .val value') ∧
    (∀ genv (value : SemanticPrimitivesHOL.Value) (result : Result β FlatSem.Value),
      ResultRel payload genv (.err (.raise value)) result ↔
        ∃ value', ValueRel genv value value' ∧ result = .err (.raise value')) ∧
    (∀ genv (_unused : γ) (result : Result β FlatSem.Value) (error : Abort),
      ResultRel payload genv (.err (.abort error)) result ↔ result = .err (.abort error)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro genv value result
    constructor
    · intro related
      cases related with
      | value relation => exact ⟨_, relation, rfl⟩
    · rintro ⟨value', relation, rfl⟩
      exact .value relation
  · intro genv value result
    constructor
    · intro related
      cases related with
      | raise relation => exact ⟨_, relation, rfl⟩
    · rintro ⟨value', relation, rfl⟩
      exact .raise relation
  · intro genv _ result error
    constructor
    · intro related
      cases related
      rfl
    · intro equal
      subst result
      exact .abort error

/-- Related successful expression lists use pointwise value correspondence. -/
abbrev EvalResultRel := ResultRel (fun genv => List.Forall₂ (ValueRel genv))

/-- Fixed-global expression simulation used inside the growing simulation for
the source-to-flat correctness proof. -/
def ExprSim {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F) (expr : AstHOL.Exp) : Prop :=
  let source := EvaluateHOL.evaluate sourceState sourceEnv [expr]
  let flat := FlatSem.evaluate flatEnv flatState [compileExp trace compMap expr]
  EvalResultRel genv source.2 flat.2 ∧ StateRel genv source.1 flat.1

/-- Simulation of expression lists at a fixed global relation. -/
def ExprListSim {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (expressions : List AstHOL.Exp) : Prop :=
  let source := EvaluateHOL.evaluate sourceState sourceEnv expressions
  let flat := FlatSem.evaluate flatEnv flatState (compileExps trace compMap expressions)
  EvalResultRel genv source.2 flat.2 ∧ StateRel genv source.1 flat.1

/-- A literal is simulated by the compiled literal. -/
theorem exprSim_literal {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (lit : Lit) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.lit lit) := by
  simp only [ExprSim, EvaluateHOL.evaluate, compileExp, FlatSem.evaluate]
  exact ⟨.value (.cons (.literal genv lit) .nil), statesRel⟩

/-- Function creation preserves simulation when the captured local
environment and the unshadowed global environment satisfy their relations. -/
theorem exprSim_function {C F : Type} (genv : GlobalEnv) (compMap : Environment)
    (globalEnv : SemEnv SemanticPrimitivesHOL.Value)
    (sourceLocal : Namespace ModN VarN SemanticPrimitivesHOL.Value)
    (flatEnv : FlatSem.Environment FlatSem.Value) (localRel : EnvRel genv sourceLocal flatEnv.v)
    (globalInv : GlobalEnvInv genv compMap (fun n => n ∈ flatEnv.v.map Prod.fst) globalEnv)
    (traces : List BackendCommon.Tra) (length : traces.length = flatEnv.v.length)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (trace : List VarN)
    (name : VarN) (body : AstHOL.Exp) :
    ExprSim genv { compMap with v := bindLocals traces (flatEnv.v.map Prod.fst) compMap.v } trace
      { globalEnv with v := nsAppend sourceLocal globalEnv.v } flatEnv sourceState flatState (.fn name body) := by
  have related := ValueRel.closure genv compMap globalEnv sourceLocal name body flatEnv trace (.none :: traces)
    localRel globalInv (by simpa using length)
  have closureRel : ValueRel genv (.closure { globalEnv with v := nsAppend sourceLocal globalEnv.v } name body)
      (.closure flatEnv name (compileExp trace
        { compMap with v := (nsBind name (VarName.localName .none name)
          (bindLocals traces (flatEnv.v.map Prod.fst) compMap.v)) } body)) := by
    simpa [bindLocals, nsBindList] using related
  simp only [ExprSim, EvaluateHOL.evaluate, compileExp, FlatSem.evaluate]
  exact ⟨.value (.cons closureRel .nil), statesRel⟩

/-- Tuple construction is simulated when the reversed argument list is
simulated. Values are restored to source order after evaluation. -/
theorem exprSim_tuple {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (args : List AstHOL.Exp)
    (argsSim : ExprListSim genv compMap trace sourceEnv flatEnv sourceState flatState args.reverse) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.con none args) := by
  unfold ExprListSim at argsSim
  rw [compileExps_reverse] at argsSim
  cases sourceRun : EvaluateHOL.evaluate sourceState sourceEnv args.reverse with
  | mk sourceNext sourceResult =>
    rw [sourceRun] at argsSim
    cases flatRun : FlatSem.evaluate flatEnv flatState (compileExps trace compMap args).reverse with
    | mk flatNext flatResult =>
      rw [flatRun] at argsSim
      obtain ⟨related, nextRel⟩ := argsSim
      cases related
      all_goals
        unfold ExprSim
        rw [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate, sourceRun, flatRun]
        simp only [doConCheck, ↓reduceIte, buildConv]
      case value valuesRel =>
        exact ⟨.value (.cons (valueRel_tuple genv _ _ (List.rel_reverse valuesRel)) .nil), nextRel⟩
      case raise valueRel => exact ⟨.raise valueRel, nextRel⟩
      case abort error => exact ⟨.abort error, nextRel⟩

/-- A conditional propagates a related condition error on both sides. -/
theorem exprSim_if_error {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (cond yes no : AstHOL.Exp) (sourceNext : SemanticPrimitivesHOL.State F)
    (error : ErrorResult SemanticPrimitivesHOL.Value)
    (sourceCondition : EvaluateHOL.evaluate sourceState sourceEnv [cond] = (sourceNext, .err error))
    (conditionSim : ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState cond) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.if_ cond yes no) := by
  unfold ExprSim at conditionSim
  rw [sourceCondition] at conditionSim
  cases flatCondition : FlatSem.evaluate flatEnv flatState [compileExp trace compMap cond] with
  | mk flatNext flatResult =>
    rw [flatCondition] at conditionSim
    obtain ⟨resultRel, nextRel⟩ := conditionSim
    cases resultRel
    all_goals
      unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [cond] []).1, sourceCondition]
      rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flatState
        [compileExp trace compMap cond] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatCondition]
      exact ⟨by constructor <;> assumption, nextRel⟩

/-- A logical expression propagates a related left-operand error. -/
theorem exprSim_log_error {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (op : Lop) (left right : AstHOL.Exp) (sourceNext : SemanticPrimitivesHOL.State F)
    (error : ErrorResult SemanticPrimitivesHOL.Value)
    (sourceLeft : EvaluateHOL.evaluate sourceState sourceEnv [left] = (sourceNext, .err error))
    (leftSim : ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState left) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.log op left right) := by
  unfold ExprSim at leftSim
  rw [sourceLeft] at leftSim
  cases flatLeft : FlatSem.evaluate flatEnv flatState [compileExp trace compMap left] with
  | mk flatNext flatResult =>
    rw [flatLeft] at leftSim
    obtain ⟨resultRel, nextRel⟩ := leftSim
    cases resultRel
    all_goals
      unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [left] []).1, sourceLeft]
      cases op <;> rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flatState
        [compileExp trace compMap left] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatLeft]
      all_goals exact ⟨by constructor <;> assumption, nextRel⟩

/-- Raise simulation from the operand induction hypothesis. -/
theorem exprSim_raise {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F) (body : AstHOL.Exp)
    (bodySim : ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState body) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.raise body) := by
  unfold ExprSim at bodySim
  cases sourceRun : EvaluateHOL.evaluate sourceState sourceEnv [body] with
  | mk sourceNext sourceResult =>
    rw [sourceRun] at bodySim
    cases flatRun : FlatSem.evaluate flatEnv flatState [compileExp trace compMap body] with
    | mk flatNext flatResult =>
      rw [flatRun] at bodySim
      obtain ⟨related, nextRel⟩ := bodySim
      cases related
      all_goals
        unfold ExprSim
        rw [EvaluateHOL.evaluate, sourceRun, compileExp, FlatSem.evaluate, flatRun]
      case raise valueRel => exact ⟨.raise valueRel, nextRel⟩
      case abort error => exact ⟨.abort error, nextRel⟩
      case value valuesRel =>
        obtain ⟨value, rfl⟩ := EvaluateProps.evaluateSingFull sourceState sourceEnv body sourceNext _ sourceRun
        cases valuesRel with
        | cons valueRel tail =>
          cases tail with
          | nil =>
            simp only [EvaluateHOL.headValue, Flapjack.holHd]
            exact ⟨.raise valueRel, nextRel⟩

end Flapjack.Compiler.Backend.SourceToFlat
