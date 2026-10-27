import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateCases
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.OracleInvariant
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.FiniteMapGrowth
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

/-- Expression-list results remain related after global growth. -/
theorem evalResultRel_growth (old new : GlobalEnv) (growth : GlobalGrowth old new)
    (source : Result (List SemanticPrimitivesHOL.Value) SemanticPrimitivesHOL.Value)
    (flat : Result (List FlatSem.Value) FlatSem.Value)
    (related : EvalResultRel old source flat) : EvalResultRel new source flat := by
  cases related with
  | value rel => exact .value (valueList_growth old new growth _ _ rel)
  | raise rel => exact .raise (valueRel_growth old new growth _ _ rel)
  | abort error => exact .abort error

/-- A simulation remains valid when its global relation grows. The evaluator
runs are unchanged; this weakens only their result and state relations. -/
theorem exprSim_growth {C F : Type} (old new : GlobalEnv) (growth : GlobalGrowth old new)
    (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F) (expr : AstHOL.Exp)
    (sim : ExprSim old compMap trace sourceEnv flatEnv sourceState flatState expr) :
    ExprSim new compMap trace sourceEnv flatEnv sourceState flatState expr := by
  exact ⟨evalResultRel_growth old new growth _ _ sim.1, stateRel_growth old new growth _ _ sim.2⟩

/-- Expression-list simulations admit the same weakening. -/
theorem exprListSim_growth {C F : Type} (old new : GlobalEnv) (growth : GlobalGrowth old new)
    (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F) (exprs : List AstHOL.Exp)
    (sim : ExprListSim old compMap trace sourceEnv flatEnv sourceState flatState exprs) :
    ExprListSim new compMap trace sourceEnv flatEnv sourceState flatState exprs := by
  exact ⟨evalResultRel_growth old new growth _ _ sim.1, stateRel_growth old new growth _ _ sim.2⟩

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

/-- A Boolean left operand of a logical expression either selects the right
operand or returns the short-circuit Boolean, preserving related states. -/
theorem exprSim_log_boolean {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (op : Lop) (left right : AstHOL.Exp) (ok : genvCOk genv.c) (b : Bool)
    (sourceNext : SemanticPrimitivesHOL.State F)
    (sourceLeft : EvaluateHOL.evaluate sourceState sourceEnv [left] =
      (sourceNext, .val [SemanticPrimitivesHOL.boolValue b]))
    (leftSim : ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState left)
    (rightSim : ∀ (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F),
      StateRel genv source flat → ExprSim genv compMap trace sourceEnv flatEnv source flat right) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.log op left right) := by
  unfold ExprSim at leftSim
  rw [sourceLeft] at leftSim
  cases flatLeft : FlatSem.evaluate flatEnv flatState [compileExp trace compMap left] with
  | mk flatNext flatResult =>
    rw [flatLeft] at leftSim
    obtain ⟨resultRel, nextRel⟩ := leftSim
    cases resultRel with
    | value valuesRel =>
      cases valuesRel with
      | cons head tail =>
        cases tail with
        | nil =>
          have flatBoolean := (boolValueRel_iff genv ok b _).mp head
          subst_vars
          have sourceStep : EvaluateHOL.evaluate sourceState sourceEnv [.log op left right] =
              if (op = .andalso ∧ b = true) ∨ (op = .orelse ∧ b = false) then
                EvaluateHOL.evaluate sourceNext sourceEnv [right]
              else (sourceNext, .val [SemanticPrimitivesHOL.boolValue b]) := by
            rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [left] []).1, sourceLeft]
            simp only [EvaluateHOL.headValue, Flapjack.holHd]
            cases op <;> cases b <;> rfl
          have flatStep : FlatSem.evaluate flatEnv flatState [compileExp trace compMap (.log op left right)] =
              if (op = .andalso ∧ b = true) ∨ (op = .orelse ∧ b = false) then
                FlatSem.evaluate flatEnv flatNext [compileExp trace compMap right]
              else (flatNext, .val [FlatSem.boolValue b]) := by
            cases op <;> cases b <;>
              rw [compileExp, FlatSem.evaluate,
                (FlatSem.fixClock_evaluations flatEnv flatState [compileExp trace compMap left]
                  (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatLeft] <;>
              simp [FlatSem.doIf, FlatSem.boolValue, BackendCommon.boolToTag,
                BackendCommon.trueTag, BackendCommon.falseTag, FlatLang.boolId,
                FlatLang.mkBool, FlatSem.evaluate]
          unfold ExprSim
          rw [sourceStep, flatStep]
          cases op <;> cases b
          all_goals simp only [reduceCtorEq, Bool.false_eq_true, Bool.true_eq_false, false_and, true_and,
            false_or, true_or, ↓reduceIte]
          all_goals first
            | exact ⟨.value (.cons (boolValue_related genv ok _) .nil), nextRel⟩
            | simpa [ExprSim] using rightSim sourceNext flatNext nextRel

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

/-- Logical-expression simulation for every source execution that does not
end in a type error. The hypotheses are the operand induction simulations. -/
theorem exprSim_log {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (op : Lop) (left right : AstHOL.Exp) (ok : genvCOk genv.c)
    (leftSim : ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState left)
    (notTypeError : ∀ next : SemanticPrimitivesHOL.State F,
      EvaluateHOL.evaluate sourceState sourceEnv [.log op left right] ≠ (next, .err (.abort .typeError)))
    (rightSim : ∀ (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F),
      StateRel genv source flat → ExprSim genv compMap trace sourceEnv flatEnv source flat right) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.log op left right) := by
  cases leftRun : EvaluateHOL.evaluate sourceState sourceEnv [left] with
  | mk next result =>
    cases result with
    | err error =>
      exact exprSim_log_error genv compMap trace sourceEnv flatEnv sourceState flatState op left right
        next error leftRun leftSim
    | val values =>
      obtain ⟨value, rfl⟩ := EvaluateProps.evaluateSingFull sourceState next sourceEnv left values leftRun
      cases selection : SemanticPrimitivesHOL.doLog op value right with
      | none =>
        have bad : EvaluateHOL.evaluate sourceState sourceEnv [.log op left right] =
            (next, .err (.abort .typeError)) := by
          rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [left] []).1, leftRun]
          simp only [EvaluateHOL.headValue, Flapjack.holHd]
          rw [selection]
          rfl
        exact (notTypeError next bad).elim
      | some result =>
        obtain ⟨b, valueEq⟩ := SemanticPrimitivesHOL.doLog_success_boolean op value right result selection
        subst value
        exact exprSim_log_boolean genv compMap trace sourceEnv flatEnv sourceState flatState op left right ok b
          next leftRun leftSim rightSim

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

/-- An exception handler preserves a simulated body result when the body does
not raise an exception; its rows are irrelevant for values and aborts. -/
theorem exprSim_handle_unraised {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F) (body : AstHOL.Exp)
    (rows : List (Pat × AstHOL.Exp))
    (bodySim : ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState body)
    (notRaised : ∀ value, (EvaluateHOL.evaluate sourceState sourceEnv [body]).2 ≠ .err (.raise value)) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.handle body rows) := by
  unfold ExprSim at bodySim
  cases sourceRun : EvaluateHOL.evaluate sourceState sourceEnv [body] with
  | mk sourceNext sourceResult =>
    rw [sourceRun] at bodySim
    cases flatRun : FlatSem.evaluate flatEnv flatState [compileExp trace compMap body] with
    | mk flatNext flatResult =>
      rw [flatRun] at bodySim
      obtain ⟨related, nextRel⟩ := bodySim
      cases related with
      | value valuesRel =>
        unfold ExprSim
        rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [body] []).1, sourceRun]
        rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flatState
          [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
        exact ⟨.value valuesRel, nextRel⟩
      | abort error =>
        unfold ExprSim
        rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [body] []).1, sourceRun]
        rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flatState
          [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
        exact ⟨.abort error, nextRel⟩
      | raise valueRel =>
        rename_i sourceValue flatValue
        have contradiction := notRaised sourceValue
        rw [sourceRun] at contradiction
        exact (contradiction rfl).elim

/-- An empty exception handler preserves the expression's result, including
re-raising an exception after no rows match. -/
theorem exprSim_handle_empty {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F) (body : AstHOL.Exp)
    (bodySim : ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState body) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.handle body []) := by
  unfold ExprSim at bodySim
  cases sourceRun : EvaluateHOL.evaluate sourceState sourceEnv [body] with
  | mk sourceNext sourceResult =>
    rw [sourceRun] at bodySim
    cases flatRun : FlatSem.evaluate flatEnv flatState [compileExp trace compMap body] with
    | mk flatNext flatResult =>
      rw [flatRun] at bodySim
      obtain ⟨related, nextRel⟩ := bodySim
      cases related with
      | value valuesRel =>
        unfold ExprSim
        rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [body] []).1, sourceRun]
        rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flatState
          [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
        exact ⟨.value valuesRel, nextRel⟩
      | abort error =>
        unfold ExprSim
        rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [body] []).1, sourceRun]
        rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flatState
          [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
        exact ⟨.abort error, nextRel⟩
      | raise valueRel =>
        unfold ExprSim
        rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [body] []).1, sourceRun]
        rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flatState
          [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
        simp only [List.map_nil, canPmatchAll, List.all_nil, ↓reduceIte, EvaluateHOL.evaluateMatch,
          compilePes, FlatSem.selectRow, FlatSem.pmatchRows]
        exact ⟨.raise valueRel, nextRel⟩

/-- An anonymous let evaluates its body in the unchanged environments after
the first expression succeeds, and propagates related errors otherwise. -/
theorem exprSim_let_anonymous {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (first body : AstHOL.Exp)
    (firstSim : ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState first)
    (bodySim : ∀ (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F),
      StateRel genv source flat → ExprSim genv compMap trace sourceEnv flatEnv source flat body) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.let_ none first body) := by
  unfold ExprSim at firstSim
  cases sourceRun : EvaluateHOL.evaluate sourceState sourceEnv [first] with
  | mk sourceNext sourceResult =>
    rw [sourceRun] at firstSim
    cases flatRun : FlatSem.evaluate flatEnv flatState [compileExp trace compMap first] with
    | mk flatNext flatResult =>
      rw [flatRun] at firstSim
      obtain ⟨related, nextRel⟩ := firstSim
      cases related with
      | raise valueRel =>
        unfold ExprSim
        rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [first] []).1, sourceRun]
        rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flatState
          [compileExp trace compMap first] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
        exact ⟨.raise valueRel, nextRel⟩
      | abort error =>
        unfold ExprSim
        rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [first] []).1, sourceRun]
        rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flatState
          [compileExp trace compMap first] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
        exact ⟨.abort error, nextRel⟩
      | value _ =>
        unfold ExprSim
        rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [first] []).1, sourceRun]
        rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flatState
          [compileExp trace compMap first] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
        simpa [ExprSim, nsOptBind] using bodySim sourceNext flatNext nextRel

/-- A named let binding preserves simulation when the binding expression and
body simulations hold for related values and states. The body uses the
extended source, flat, and compilation environments. -/
theorem exprSim_let_named {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (name : VarN) (first body : AstHOL.Exp)
    (firstSim : ExprSim genv compMap (name :: trace) sourceEnv flatEnv sourceState flatState first)
    (bodySim : ∀ (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
      (value : SemanticPrimitivesHOL.Value) (flatValue : FlatSem.Value),
      StateRel genv source flat → ValueRel genv value flatValue →
      ExprSim genv { compMap with v := nsBind name (.localName .none name) compMap.v } trace
        { sourceEnv with v := nsBind name value sourceEnv.v }
        { flatEnv with v := (name, flatValue) :: flatEnv.v } source flat body) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.let_ (some name) first body) := by
  unfold ExprSim at firstSim
  cases sourceRun : EvaluateHOL.evaluate sourceState sourceEnv [first] with
  | mk sourceNext sourceResult =>
    rw [sourceRun] at firstSim
    cases flatRun : FlatSem.evaluate flatEnv flatState [compileExp (name :: trace) compMap first] with
    | mk flatNext flatResult =>
      rw [flatRun] at firstSim
      obtain ⟨related, nextRel⟩ := firstSim
      cases sourceResult with
      | err error =>
        cases error with
        | raise value =>
          cases related with
          | raise valueRel =>
            unfold ExprSim
            rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [first] []).1, sourceRun]
            rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flatState
              [compileExp (name :: trace) compMap first] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
            exact ⟨.raise valueRel, nextRel⟩
        | abort error =>
          cases related with
          | abort =>
            unfold ExprSim
            rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [first] []).1, sourceRun]
            rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flatState
              [compileExp (name :: trace) compMap first] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
            exact ⟨.abort error, nextRel⟩
      | val values =>
        obtain ⟨value, rfl⟩ := EvaluateProps.evaluateSingFull sourceState sourceNext sourceEnv first values sourceRun
        cases related with
        | value valuesRel =>
          cases valuesRel with
          | cons valueRel tail =>
            cases tail with
            | nil =>
              unfold ExprSim
              rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate sourceState sourceEnv [first] []).1, sourceRun]
              rw [compileExp, FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flatState
                [compileExp (name :: trace) compMap first] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
              simp only [EvaluateHOL.headValue, Flapjack.holHd, nsOptBind]
              simpa [ExprSim] using bodySim sourceNext flatNext value _ nextRel valueRel

end Flapjack.Compiler.Backend.SourceToFlat
