import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateCases
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PrimitiveType
import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateClock
import Flapjack.EvaluateHOL.ClockFull
import Flapjack.EvaluateProps.Length

/-! Composition of expression simulations over the factored source-to-flat
relations. These declarations are untagged until the relations and the flat
evaluator have completed HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL

/-- Relate successful results using an arbitrary payload relation, raised
exceptions using the value relation, and identical aborts. -/
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

/-- A related local binding is simulated by its compiled local lookup. -/
theorem exprSim_local {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (envRel : EnvRel genv sourceEnv.v flatEnv.v)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (name : VarN) (t : BackendCommon.Tra)
    (compiled : nsLookup compMap.v (.short name) = some (.localName t name))
    (source : SemanticPrimitivesHOL.Value) (lookup : nsLookup sourceEnv.v (.short name) = some source) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.var (.short name)) := by
  obtain ⟨flat, sourceRun, flatRun, valueRel, nextRel⟩ :=
    evaluate_local_unbounded genv compMap sourceEnv flatEnv envRel sourceState flatState statesRel
      trace name t compiled source lookup
  unfold ExprSim
  rw [sourceRun, flatRun]
  exact ⟨.value (.cons valueRel .nil), nextRel⟩

/-- A related global binding is simulated by its compiled global lookup. -/
theorem exprSim_global {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (globalsEq : flatState.globals = genv.v)
    (id : Ident ModN VarN) (source : SemanticPrimitivesHOL.Value)
    (lookup : nsLookup sourceEnv.v id = some source) (related : GlobalLookupRel genv compMap id source) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.var id) := by
  obtain ⟨flat, sourceRun, flatRun, valueRel, nextRel⟩ :=
    evaluate_global_unbounded genv compMap sourceEnv flatEnv sourceState flatState statesRel globalsEq
      trace id source lookup related
  unfold ExprSim
  rw [sourceRun, flatRun]
  exact ⟨.value (.cons valueRel .nil), nextRel⟩

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

/-- A singleton expression simulation is an expression-list simulation. -/
theorem exprListSim_singleton {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F) (expr : AstHOL.Exp)
    (sim : ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState expr) :
    ExprListSim genv compMap trace sourceEnv flatEnv sourceState flatState [expr] := by
  simpa [ExprSim, ExprListSim, compileExps] using sim

/-- The empty expression list preserves related states. -/
theorem exprListSim_nil {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) :
    ExprListSim genv compMap trace sourceEnv flatEnv sourceState flatState [] := by
  simp only [ExprListSim, EvaluateHOL.evaluate, compileExps, FlatSem.evaluate]
  exact ⟨.value .nil, statesRel⟩

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

/-- A two-literal tuple gives a concrete composition of expression-list and
tuple simulation, including right-to-left argument evaluation. -/
theorem exprSim_tuple_literals {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (first second : Lit) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.con none [.lit first, .lit second]) := by
  apply exprSim_tuple
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  apply exprListSim_cons
  · exact exprSim_literal genv compMap trace sourceEnv flatEnv sourceState flatState statesRel second
  · intro source flat related
    apply exprListSim_singleton
    exact exprSim_literal genv compMap trace sourceEnv flatEnv source flat related first

/-- Conditional simulation for a successfully evaluated Boolean condition.
The condition and both branches are supplied as expression induction
hypotheses. Error outcomes and the full pass invariants remain separate. -/
theorem exprSim_if_boolean {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (cond yes no : AstHOL.Exp) (ok : genvCOk genv.c) (b : Bool)
    (sourceNext : SemanticPrimitivesHOL.State F)
    (sourceCondition : EvaluateHOL.evaluate sourceState sourceEnv [cond] =
      (sourceNext, .val [SemanticPrimitivesHOL.boolValue b]))
    (conditionSim : ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState cond)
    (yesSim : ∀ (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F),
      StateRel genv source flat → ExprSim genv compMap trace sourceEnv flatEnv source flat yes)
    (noSim : ∀ (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F),
      StateRel genv source flat → ExprSim genv compMap trace sourceEnv flatEnv source flat no) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.if_ cond yes no) := by
  unfold ExprSim at conditionSim
  rw [sourceCondition] at conditionSim
  cases flatCondition : FlatSem.evaluate flatEnv flatState [compileExp trace compMap cond] with
  | mk flatNext flatResult =>
    rw [flatCondition] at conditionSim
    obtain ⟨resultRel, nextRel⟩ := conditionSim
    cases resultRel with
    | value valuesRel =>
      cases valuesRel with
      | cons head tail =>
        cases tail with
        | nil =>
          have flatBoolean := (boolValueRel_iff genv ok b _).mp head
          subst_vars
          have sourceStep : EvaluateHOL.evaluate sourceState sourceEnv [.if_ cond yes no] =
              EvaluateHOL.evaluate sourceNext sourceEnv [if b then yes else no] := by
            rw [EvaluateHOL.evaluate]
            rw [(EvaluateHOL.fixClockEvaluate sourceState sourceEnv [cond] []).1, sourceCondition]
            simp only [EvaluateHOL.headValue, Flapjack.holHd]
            rw [SemanticPrimitivesHOL.doIf_boolValue]
          have flatStep : FlatSem.evaluate flatEnv flatState [compileExp trace compMap (.if_ cond yes no)] =
              FlatSem.evaluate flatEnv flatNext [compileExp trace compMap (if b then yes else no)] := by
            rw [compileExp, FlatSem.evaluate]
            rw [(FlatSem.fixClock_evaluations flatEnv flatState [compileExp trace compMap cond]
              (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatCondition]
            cases b <;> simp [FlatSem.doIf, FlatSem.boolValue, BackendCommon.boolToTag,
              BackendCommon.trueTag, BackendCommon.falseTag, FlatLang.boolId]
          unfold ExprSim
          rw [sourceStep, flatStep]
          cases b with
          | false => simpa [ExprSim] using noSim sourceNext flatNext nextRel
          | true => simpa [ExprSim] using yesSim sourceNext flatNext nextRel

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

/-- Conditional simulation for all non-type-error source outcomes. -/
theorem exprSim_if {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (cond yes no : AstHOL.Exp) (ok : genvCOk genv.c)
    (conditionSim : ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState cond)
    (notTypeError : ∀ next : SemanticPrimitivesHOL.State F,
      EvaluateHOL.evaluate sourceState sourceEnv [.if_ cond yes no] ≠ (next, .err (.abort .typeError)))
    (yesSim : ∀ (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F),
      StateRel genv source flat → ExprSim genv compMap trace sourceEnv flatEnv source flat yes)
    (noSim : ∀ (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F),
      StateRel genv source flat → ExprSim genv compMap trace sourceEnv flatEnv source flat no) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.if_ cond yes no) := by
  cases conditionRun : EvaluateHOL.evaluate sourceState sourceEnv [cond] with
  | mk next result =>
    cases result with
    | err error =>
      exact exprSim_if_error genv compMap trace sourceEnv flatEnv sourceState flatState cond yes no
        next error conditionRun conditionSim
    | val values =>
      obtain ⟨value, rfl⟩ := EvaluateProps.evaluateSingFull sourceState next sourceEnv cond values conditionRun
      cases selection : SemanticPrimitivesHOL.doIf value yes no with
      | none =>
        have bad : EvaluateHOL.evaluate sourceState sourceEnv [.if_ cond yes no] =
            (next, .err (.abort .typeError)) := by
          rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [cond] []).1, conditionRun]
          simp only [EvaluateHOL.headValue, Flapjack.holHd]
          rw [selection]
          rfl
        exact (notTypeError next bad).elim
      | some branch =>
        obtain ⟨b, valueEq, _⟩ := SemanticPrimitivesHOL.doIf_success_boolean value yes no branch selection
        subst value
        exact exprSim_if_boolean genv compMap trace sourceEnv flatEnv sourceState flatState cond yes no ok b
          next conditionRun conditionSim yesSim noSim

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
