module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBounded
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalEnvironment

@[expose] public section

/-! Clock-bounded primitive simulation over preliminary source-to-flat relations. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- Operand errors propagate before an application whose successful operands
are rejected by its concrete source operation. The public bad-arity cases
below discharge both compilation and operation-rejection facts.
This Flapjack proof factoring has no separate HOL declaration. -/
private theorem localEnvBounded_rejectedApp {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (op : Op) (flatOp : FlatLang.Op) (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr)
    (compiled : ∀ trace compMap, compileExp trace compMap (.app op args) =
      .app .none flatOp (compileExps trace compMap args))
    (rejected : ∀ (state : State F) (values : List Value), values.length = args.length →
      (op = .opapp ∧ doOpApp values.reverse = none) ∨
      (op = .thunkOp .forceThunk ∧ destThunk values.reverse state.refs = .notThunk) ∨
      (getOpClass op = .simple ∧ doApp (state.refs, state.ffi) op values.reverse = none)) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app op args) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv args.reverse ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app op args] = _
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform limit args.reverse
    (fun expr member => each expr (List.mem_reverse.mp member)) genv start finish other source flat baseEnv sourceLocal flatEnv traces
    trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
  unfold ExprListSim at argsSim
  rw [compileExps_reverse] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv args.reverse = sourceResult at argsSim post
  obtain ⟨sourceNext, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat (compileExps trace compMap args).reverse = flatResult at argsSim post
  obtain ⟨flatNext, flatResult⟩ := flatResult
  obtain ⟨resultRel, states⟩ := argsSim
  cases resultRel with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      rw [compiled trace compMap]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        (compileExps trace compMap args).reverse (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      trivial
  | raise related =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      rw [compiled trace compMap]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        (compileExps trace compMap args).reverse (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.raise related, states⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      rw [compiled trace compMap]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        (compileExps trace compMap args).reverse (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact post
  | @value sourceValues flatValues related =>
    have length := EvaluateProps.evaluateLengthFull source sourceNext sourceEnv args.reverse sourceValues sourceRun
    apply False.elim
    apply safe sourceNext
    change EvaluateHOL.evaluate source sourceEnv [.app op args] = _
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
    rcases rejected sourceNext sourceValues (by simpa using length) with
      ⟨rfl, bad⟩ | ⟨rfl, bad⟩ | ⟨simple, bad⟩
    all_goals simp_all [getOpClass, EvaluateHOL.typeError]

/-- Malformed thunk forcing still propagates errors from its operands. -/
theorem localEnvBounded_forceThunk_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (args : List AstHOL.Exp) (badArity : args.length ≠ 1)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.thunkOp .forceThunk) args) := by
  apply localEnvBounded_rejectedApp interp transform limit (.thunkOp .forceThunk) (.src (.thunkOp .forceThunk)) args each
  · intro trace compMap; rfl
  · intro state values length
    have bad : values.reverse.length ≠ 1 := by simpa [length] using badArity
    have rejected : destThunk values.reverse state.refs = .notThunk := by
      cases vals : values.reverse with
      | nil => simp [destThunk]
      | cons first rest =>
        cases rest with
        | nil => simp [vals] at bad
        | cons second rest => simp [destThunk]
    exact Or.inr (Or.inl ⟨rfl, rejected⟩)

/-- Malformed environment-ID applications preserve operand errors. -/
theorem localEnvBounded_envId_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (args : List AstHOL.Exp) (badArity : args.length ≠ 1)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .envId args) := by
  apply localEnvBounded_rejectedApp interp transform limit (.envId) (.el 0) args each
  · intro trace compMap
    cases args with
    | nil => rfl
    | cons first rest =>
      cases rest with
      | nil => simp at badArity
      | cons second rest => rfl
  · intro state values length
    have bad : values.reverse.length ≠ 1 := by simpa [length] using badArity
    have rejected : doApp (state.refs, state.ffi) .envId values.reverse = none := by
      cases vals : values.reverse with
      | nil => simp [doApp, doAppNumericCore, doAppBasic]
      | cons first rest =>
        cases rest with
        | nil => simp [vals] at bad
        | cons second rest => simp [doApp, doAppNumericCore, doAppBasic]
    exact Or.inr (Or.inr ⟨rfl, rejected⟩)

/-- Malformed function applications propagate operand errors. -/
theorem localEnvBounded_opapp_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (args : List AstHOL.Exp) (badArity : args.length ≠ 2)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .opapp args) := by
  apply localEnvBounded_rejectedApp interp transform limit (.opapp) (.src .opapp) args each
  · intro trace compMap; rfl
  · intro state values length
    have bad : values.reverse.length ≠ 2 := by simpa [length] using badArity
    have rejected : doOpApp values.reverse = none := by
      cases vals : values.reverse with
      | nil => simp [doOpApp]
      | cons first rest =>
        cases rest with
        | nil => simp [doOpApp]
        | cons second rest =>
          cases rest with
          | nil => simp [vals] at bad
          | cons third rest => simp [doOpApp]
    exact Or.inl ⟨rfl, rejected⟩

/-- Compose localEnvBounded_tuple over arbitrary related local environments. -/
theorem localEnvBounded_tuple {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.con none args) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  change LocalExpressionStep interp transform genv start finish other source flat sourceEnv flatEnv trace compMap gen
    (.con none args)
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv args.reverse ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.con none args] = _
    simp [EvaluateHOL.evaluate, doConCheck, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform limit args.reverse
    (fun expr member => each expr (List.mem_reverse.mp member)) genv start finish other source flat baseEnv sourceLocal flatEnv traces
    trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
  refine ⟨nextGenv, exprSim_tuple nextGenv compMap trace sourceEnv flatEnv source flat args argsSim, ?_⟩
  unfold ExprListSim at argsSim
  rw [compileExps_reverse] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv args.reverse = sourceResult at argsSim post ⊢
  obtain ⟨sourceNext, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat (compileExps trace compMap args).reverse = flatResult at argsSim post ⊢
  obtain ⟨flatNext, flatResult⟩ := flatResult
  obtain ⟨resultRel, _⟩ := argsSim
  cases resultRel with
  | abort error =>
    simp [EvaluateHOL.evaluate, doConCheck, sourceRun]
  | raise related =>
    simpa [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate, doConCheck, sourceRun, flatRun] using post
  | value related =>
    simpa [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate, doConCheck, buildConv, sourceRun, flatRun] using post


/-- Compose localEnvBounded_constructor over arbitrary related local environments. -/
theorem localEnvBounded_constructor {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (id : Ident ModN ConN) (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.con (some id) args) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  change LocalExpressionStep interp transform genv start finish other source flat sourceEnv flatEnv trace compMap gen
    (.con (some id) args)
  have check : doConCheck sourceEnv.c (some id) args.length = true := by
    cases h : doConCheck sourceEnv.c (some id) args.length with
    | true => rfl
    | false =>
      have bad : EvaluateHOL.evaluate source sourceEnv [.con (some id) args] =
          (source, .err (.abort .typeError)) := by
        simp [EvaluateHOL.evaluate, h, EvaluateHOL.typeError]
      exact False.elim (safe source bad)
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv args.reverse ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.con (some id) args] = _
    simp [EvaluateHOL.evaluate, check, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform limit args.reverse
    (fun expr member => each expr (List.mem_reverse.mp member)) genv start finish other source flat baseEnv sourceLocal flatEnv traces
    trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
  have sim : ExprSim nextGenv compMap trace sourceEnv flatEnv source flat (.con (some id) args) := by
    generalize sourceRun : EvaluateHOL.evaluate source sourceEnv args.reverse = result at post
    obtain ⟨nextSource, result⟩ := result
    cases result with
    | err error =>
      cases error with
      | abort abort =>
        exact exprSim_constructor_abort nextGenv compMap trace sourceEnv flatEnv source flat (some id) args
          check argsSim nextSource abort sourceRun
      | raise value =>
        have growth : GlobalGrowth genv nextGenv := post.1
        have nextInv := globalEnvInv_growth genv nextGenv growth baseMap (fun n => n ∈ flatEnv.v.map Prod.fst) baseEnv envInv
        cases lookup : nsLookup sourceEnv.c id with
        | none => simp [doConCheck, lookup] at check
        | some entry =>
          obtain ⟨arity, stamp⟩ := entry
          have same : args.length = arity := by simpa [doConCheck, lookup] using check
          subst arity
          cases nextInv with
          | intro _ _ _ _ constructors =>
            obtain ⟨cn, group, compiled, stampLookup, _⟩ := constructors id args.length stamp lookup
            exact exprSim_constructor_local_valid nextGenv compMap trace sourceEnv flatEnv source flat id args stamp
              lookup ⟨cn, group, compiled, stampLookup⟩ argsSim
    | val values =>
      have growth : GlobalGrowth genv nextGenv := post.1
      have nextInv := globalEnvInv_growth genv nextGenv growth baseMap (fun n => n ∈ flatEnv.v.map Prod.fst) baseEnv envInv
      cases lookup : nsLookup sourceEnv.c id with
      | none => simp [doConCheck, lookup] at check
      | some entry =>
        obtain ⟨arity, stamp⟩ := entry
        have same : args.length = arity := by simpa [doConCheck, lookup] using check
        subst arity
        cases nextInv with
        | intro _ _ _ _ constructors =>
          obtain ⟨cn, group, compiled, stampLookup, _⟩ := constructors id args.length stamp lookup
          exact exprSim_constructor_local_valid nextGenv compMap trace sourceEnv flatEnv source flat id args stamp
            lookup ⟨cn, group, compiled, stampLookup⟩ argsSim
  refine ⟨nextGenv, sim, ?_⟩
  unfold ExprListSim at argsSim
  rw [compileExps_reverse] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv args.reverse = sourceResult at argsSim post ⊢
  obtain ⟨sourceNext, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat (compileExps trace compMap args).reverse = flatResult at argsSim post ⊢
  obtain ⟨flatNext, flatResult⟩ := flatResult
  obtain ⟨resultRel, _⟩ := argsSim
  cases resultRel with
  | abort error => simp [EvaluateHOL.evaluate, check, sourceRun]
  | raise related => simpa [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate, check, sourceRun, flatRun] using post
  | @value sourceValues flatValues related =>
    cases built : buildConv sourceEnv.c (some id) sourceValues.reverse with
    | none =>
      have bad : EvaluateHOL.evaluate source sourceEnv [.con (some id) args] =
          (sourceNext, .err (.abort .typeError)) := by
        simp [EvaluateHOL.evaluate, check, sourceRun, built, EvaluateHOL.typeError]
      exact False.elim (safe sourceNext bad)
    | some value =>
      simpa [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate, check, sourceRun, flatRun, built] using post



end Flapjack.Compiler.Backend.SourceToFlat
