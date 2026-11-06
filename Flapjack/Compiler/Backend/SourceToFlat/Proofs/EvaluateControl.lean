import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateCases
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvalOracleSimulation
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.FiniteMapGrowth
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PrimitiveType
import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateClock
import Flapjack.EvaluateHOL.ClockFull
import Flapjack.EvaluateProps.Length

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

/-- Related successful expression lists use pointwise value correspondence. -/
abbrev EvalResultRel := ResultRel (fun genv => List.Forall₂ (ValueRel genv))

/-- Simulation for a single source expression, at a fixed global relation.
Changing global environments and the remaining pass invariants are not yet
captured by this preliminary relation. -/
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

/-- Compiling an expression list commutes with reversing its evaluation order. -/
theorem compileExps_reverse (trace : List VarN) (compMap : Environment) (expressions : List AstHOL.Exp) :
    compileExps trace compMap expressions.reverse = (compileExps trace compMap expressions).reverse := by
  have mapEq : ∀ xs : List AstHOL.Exp, compileExps trace compMap xs = xs.map (compileExp trace compMap) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons head tail ih => simp [compileExps, ih]
  simp [mapEq]

/-- A literal is simulated by the compiled literal. -/
theorem exprSim_literal {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (lit : Lit) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.lit lit) := by
  simp only [ExprSim, EvaluateHOL.evaluate, compileExp, FlatSem.evaluate]
  exact ⟨.value (.cons (.literal genv lit) .nil), statesRel⟩

/-- Type annotations preserve a simulation of the annotated expression. -/
theorem exprSim_tannot {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (expr : AstHOL.Exp) (typ : AstHOL.AstT)
    (sim : ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState expr) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.tannot expr typ) := by
  simpa only [ExprSim, EvaluateHOL.evaluate, compileExp] using sim

/-- Source-location annotations preserve a simulation of the annotated expression. -/
theorem exprSim_lannot {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (expr : AstHOL.Exp) (loc : Misc.Location.Locs)
    (sim : ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState expr) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.lannot expr loc) := by
  cases loc
  simpa only [ExprSim, EvaluateHOL.evaluate, compileExp] using sim

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
  obtain ⟨sourceRun, flatRun, related, nextRel⟩ :=
    evaluate_function_unbounded genv compMap globalEnv sourceLocal flatEnv localRel globalInv traces length
      sourceState flatState statesRel trace name body
  unfold ExprSim
  rw [sourceRun, flatRun]
  exact ⟨.value (.cons related .nil), nextRel⟩

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
      cases related with
      | value valuesRel =>
        unfold ExprSim
        rw [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate, sourceRun, flatRun]
        simp only [doConCheck, ↓reduceIte, buildConv]
        exact ⟨.value (.cons (valueRel_tuple genv _ _ (List.rel_reverse valuesRel)) .nil), nextRel⟩
      | raise valueRel =>
        unfold ExprSim
        rw [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate, sourceRun, flatRun]
        simp only [doConCheck, ↓reduceIte]
        exact ⟨.raise valueRel, nextRel⟩
      | abort error =>
        unfold ExprSim
        rw [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate, sourceRun, flatRun]
        simp only [doConCheck, ↓reduceIte]
        exact ⟨.abort error, nextRel⟩

/-- A named constructor is simulated when its source lookup has the given
arity and the global environment invariant supplies the compiled tag. -/
theorem exprSim_constructor_valid {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (id : Ident ModN ConN) (args : List AstHOL.Exp) (stamp : Stamp) (shadowers : VarN → Prop)
    (sourceLookup : nsLookup sourceEnv.c id = some (args.length, stamp))
    (globalInv : GlobalEnvInv genv compMap shadowers sourceEnv)
    (argsSim : ExprListSim genv compMap trace sourceEnv flatEnv sourceState flatState args.reverse) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.con (some id) args) := by
  cases globalInv with
  | intro _ _ _ _ constructors =>
    obtain ⟨cn, group, compiledLookup, stampLookup, _⟩ := constructors id args.length stamp sourceLookup
    have compiledCtor : typeGroupIdType (some (cn, group)) = some (cn, group.map Prod.fst) := by
      cases group with
      | none => rfl
      | some pair => cases pair; rfl
    unfold ExprListSim at argsSim
    rw [compileExps_reverse] at argsSim
    cases sourceRun : EvaluateHOL.evaluate sourceState sourceEnv args.reverse with
    | mk sourceNext sourceResult =>
      rw [sourceRun] at argsSim
      cases flatRun : FlatSem.evaluate flatEnv flatState (compileExps trace compMap args).reverse with
      | mk flatNext flatResult =>
        rw [flatRun] at argsSim
        obtain ⟨related, nextRel⟩ := argsSim
        cases related with
        | value valuesRel =>
          have lengthEq := EvaluateProps.evaluateLengthFull sourceState sourceNext sourceEnv args.reverse _ sourceRun
          simp only [List.length_reverse] at lengthEq
          unfold ExprSim
          rw [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate]
          simp only [doConCheck, sourceLookup, beq_self_eq_true, ↓reduceIte,
            Option.bind_some, compiledLookup, compiledCtor, sourceRun, flatRun, buildConv]
          apply And.intro _ nextRel
          apply ResultRel.value
          apply List.Forall₂.cons _ List.Forall₂.nil
          apply valueRel_constructor genv stamp (cn, group.map Prod.fst)
          · exact List.rel_reverse valuesRel
          · simpa [List.length_reverse, lengthEq] using stampLookup
        | raise valueRel =>
          unfold ExprSim
          rw [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate]
          simp only [doConCheck, sourceLookup, beq_self_eq_true, ↓reduceIte, sourceRun, flatRun]
          exact ⟨.raise valueRel, nextRel⟩
        | abort error =>
          unfold ExprSim
          rw [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate]
          simp only [doConCheck, sourceLookup, beq_self_eq_true, ↓reduceIte, sourceRun, flatRun]
          exact ⟨.abort error, nextRel⟩

/-- Named-constructor simulation for source executions without a type error.
The source constructor check supplies the arity required by the valid case. -/
theorem exprSim_constructor {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (id : Ident ModN ConN) (args : List AstHOL.Exp) (shadowers : VarN → Prop)
    (globalInv : GlobalEnvInv genv compMap shadowers sourceEnv)
    (notTypeError : ∀ next : SemanticPrimitivesHOL.State F,
      EvaluateHOL.evaluate sourceState sourceEnv [.con (some id) args] ≠ (next, .err (.abort .typeError)))
    (argsSim : doConCheck sourceEnv.c (some id) args.length = true →
      ExprListSim genv compMap trace sourceEnv flatEnv sourceState flatState args.reverse) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.con (some id) args) := by
  cases lookup : nsLookup sourceEnv.c id with
  | none =>
    have bad : EvaluateHOL.evaluate sourceState sourceEnv [.con (some id) args] =
        (sourceState, .err (.abort .typeError)) := by
      simp [EvaluateHOL.evaluate, doConCheck, lookup, EvaluateHOL.typeError]
    exact (notTypeError sourceState bad).elim
  | some entry =>
    obtain ⟨arity, stamp⟩ := entry
    by_cases same : args.length = arity
    · subst arity
      have valid : doConCheck sourceEnv.c (some id) args.length = true := by
        simp [doConCheck, lookup]
      exact exprSim_constructor_valid genv compMap trace sourceEnv flatEnv sourceState flatState
        id args stamp shadowers lookup globalInv (argsSim valid)
    · have bad : EvaluateHOL.evaluate sourceState sourceEnv [.con (some id) args] =
          (sourceState, .err (.abort .typeError)) := by
        simp [EvaluateHOL.evaluate, doConCheck, lookup, same, EvaluateHOL.typeError]
      exact (notTypeError sourceState bad).elim

/-- A singleton expression simulation is an expression-list simulation. -/
theorem exprListSim_singleton {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F) (expr : AstHOL.Exp)
    (sim : ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState expr) :
    ExprListSim genv compMap trace sourceEnv flatEnv sourceState flatState [expr] := by
  simpa [ExprSim, ExprListSim, compileExps] using sim

/-- Sequencing two or more expressions preserves simulation when the head and
tail induction hypotheses hold. -/
theorem exprListSim_cons {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (first second : AstHOL.Exp) (rest : List AstHOL.Exp)
    (headSim : ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState first)
    (tailSim : ∀ (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F),
      StateRel genv source flat → ExprListSim genv compMap trace sourceEnv flatEnv source flat (second :: rest)) :
    ExprListSim genv compMap trace sourceEnv flatEnv sourceState flatState (first :: second :: rest) := by
  unfold ExprSim at headSim
  cases sourceHead : EvaluateHOL.evaluate sourceState sourceEnv [first] with
  | mk sourceNext sourceResult =>
    rw [sourceHead] at headSim
    cases flatHead : FlatSem.evaluate flatEnv flatState [compileExp trace compMap first] with
    | mk flatNext flatResult =>
      rw [flatHead] at headSim
      obtain ⟨related, nextRel⟩ := headSim
      cases sourceResult with
      | err error =>
        cases error with
        | raise value =>
          cases related with
          | raise valueRel =>
            unfold ExprListSim
            rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [first] []).1, sourceHead]
            simp only [compileExps]
            rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flatState
              [compileExp trace compMap first] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatHead]
            exact ⟨.raise valueRel, nextRel⟩
        | abort error =>
          cases related with
          | abort =>
            unfold ExprListSim
            rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [first] []).1, sourceHead]
            simp only [compileExps]
            rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flatState
              [compileExp trace compMap first] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatHead]
            exact ⟨.abort error, nextRel⟩
      | val values =>
        obtain ⟨value, rfl⟩ := EvaluateProps.evaluateSingFull sourceState sourceNext sourceEnv first values sourceHead
        cases related with
        | value valuesRel =>
          cases valuesRel with
          | cons valueRel tail =>
            cases tail with
            | nil =>
              have tailRelated := tailSim sourceNext flatNext nextRel
              unfold ExprListSim at tailRelated ⊢
              rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [first] []).1, sourceHead]
              simp only [compileExps]
              rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flatState
                [compileExp trace compMap first] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatHead]
              simp only [EvaluateHOL.headValue, Flapjack.holHd]
              cases sourceTail : EvaluateHOL.evaluate sourceNext sourceEnv (second :: rest) with
              | mk sourceLast sourceTailResult =>
                cases flatTail : FlatSem.evaluate flatEnv flatNext (compileExps trace compMap (second :: rest)) with
                | mk flatLast flatTailResult =>
                  simp only [compileExps] at flatTail
                  rw [flatTail]
                  dsimp only at tailRelated
                  rw [sourceTail] at tailRelated
                  simp only [compileExps] at tailRelated
                  rw [flatTail] at tailRelated
                  obtain ⟨tailRel, lastRel⟩ := tailRelated
                  cases tailRel with
                  | value tailValues => exact ⟨.value (.cons valueRel tailValues), lastRel⟩
                  | raise errorRel => exact ⟨.raise errorRel, lastRel⟩
                  | abort error => exact ⟨.abort error, lastRel⟩

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
    cases error with
    | raise value =>
      cases resultRel with
      | raise valueRel =>
        unfold ExprSim
        rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [cond] []).1, sourceCondition]
        rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flatState
          [compileExp trace compMap cond] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatCondition]
        exact ⟨.raise valueRel, nextRel⟩
    | abort error =>
      cases resultRel with
      | abort =>
        unfold ExprSim
        rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [cond] []).1, sourceCondition]
        rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flatState
          [compileExp trace compMap cond] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatCondition]
        exact ⟨.abort error, nextRel⟩

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
    cases error with
    | raise value =>
      cases resultRel with
      | raise valueRel =>
        unfold ExprSim
        rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [left] []).1, sourceLeft]
        cases op <;> rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flatState
          [compileExp trace compMap left] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatLeft]
        all_goals exact ⟨.raise valueRel, nextRel⟩
    | abort error =>
      cases resultRel with
      | abort =>
        unfold ExprSim
        rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [left] []).1, sourceLeft]
        cases op <;> rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flatState
          [compileExp trace compMap left] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatLeft]
        all_goals exact ⟨.abort error, nextRel⟩

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
      cases sourceResult with
      | err error =>
        cases error with
        | raise value =>
          cases related with
          | raise valueRel =>
            unfold ExprSim
            rw [EvaluateHOL.evaluate, sourceRun, compileExp, FlatSem.evaluate, flatRun]
            exact ⟨.raise valueRel, nextRel⟩
        | abort error =>
          cases related with
          | abort =>
            unfold ExprSim
            rw [EvaluateHOL.evaluate, sourceRun, compileExp, FlatSem.evaluate, flatRun]
            exact ⟨.abort error, nextRel⟩
      | val values =>
        obtain ⟨value, rfl⟩ := EvaluateProps.evaluateSingFull sourceState sourceNext sourceEnv body values sourceRun
        cases related with
        | value valuesRel =>
          cases valuesRel with
          | cons valueRel tail =>
            cases tail with
            | nil =>
              unfold ExprSim
              rw [EvaluateHOL.evaluate, sourceRun, compileExp, FlatSem.evaluate, flatRun]
              simp only [EvaluateHOL.headValue, Flapjack.holHd]
              exact ⟨.raise valueRel, nextRel⟩

end Flapjack.Compiler.Backend.SourceToFlat
