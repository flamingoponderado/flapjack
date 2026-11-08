import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBoundedApp
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBounded
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalEnvironment

/-! Clock-bounded primitive simulation over preliminary source-to-flat relations. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- A simple primitive that rejects all argument lists of this length still
simulates errors raised while evaluating its arguments. The rejection premise
is discharged separately for each malformed operator and arity. -/
theorem localEnvBounded_rejectedSimple {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (op : Op) (args : List AstHOL.Exp)
    (simple : getOpClass op = .simple)
    (notEmpty : op ≠ .aallocEmpty) (notEval : op ≠ .eval) (notEnvId : op ≠ .envId)
    (rejects : ∀ (state : State F) values, values.length = args.length →
      doApp (state.refs, state.ffi) op values = none)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
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
      simp only [compileExp, notEmpty, notEval, notEnvId, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        (compileExps trace compMap args).reverse (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      trivial
  | raise related =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      simp only [compileExp, notEmpty, notEval, notEnvId, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        (compileExps trace compMap args).reverse (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.raise related, states⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      simp only [compileExp, notEmpty, notEval, notEnvId, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        (compileExps trace compMap args).reverse (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact post
  | @value sourceValues flatValues related =>
    have length := EvaluateProps.evaluateLengthFull source sourceNext sourceEnv args.reverse sourceValues sourceRun
    have rejected : doApp (sourceNext.refs, sourceNext.ffi) op sourceValues.reverse = none :=
      rejects sourceNext sourceValues.reverse (by simpa using length)
    apply False.elim
    apply safe sourceNext
    change EvaluateHOL.evaluate source sourceEnv [.app op args] = _
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
    simp [simple, rejected, EvaluateHOL.typeError]

/-- Malformed thunk forcing still propagates errors from its operands. -/
theorem localEnvBounded_forceThunk_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (args : List AstHOL.Exp) (badArity : args.length ≠ 1)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.thunkOp .forceThunk) args) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv args.reverse ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app (.thunkOp .forceThunk) args] = _
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
      simp only [compileExp, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        (compileExps trace compMap args).reverse (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      trivial
  | raise related =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      simp only [compileExp, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        (compileExps trace compMap args).reverse (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.raise related, states⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      simp only [compileExp, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        (compileExps trace compMap args).reverse (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact post
  | @value sourceValues flatValues related =>
    have length := EvaluateProps.evaluateLengthFull source sourceNext sourceEnv args.reverse sourceValues sourceRun
    have bad : sourceValues.reverse.length ≠ 1 := by simpa [length] using badArity
    have rejected : destThunk sourceValues.reverse sourceNext.refs = .notThunk := by
      cases vals : sourceValues.reverse with
      | nil => simp [destThunk]
      | cons first rest =>
        cases rest with
        | nil => simp [vals] at bad
        | cons second rest => simp [destThunk]
    apply False.elim
    apply safe sourceNext
    change EvaluateHOL.evaluate source sourceEnv [.app (.thunkOp .forceThunk) args] = _
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
    simp [getOpClass, rejected, EvaluateHOL.typeError]

/-- Malformed environment-ID applications preserve operand errors. -/
theorem localEnvBounded_envId_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (args : List AstHOL.Exp) (badArity : args.length ≠ 1)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .envId args) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have compiled : compileExp trace compMap (.app .envId args) =
      .app .none (.el 0) (compileExps trace compMap args) := by
    cases args with
    | nil => rfl
    | cons first rest =>
      cases rest with
      | nil => simp at badArity
      | cons second rest => rfl
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv args.reverse ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .envId args] = _
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
      rw [compiled]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        (compileExps trace compMap args).reverse (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      trivial
  | raise related =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      rw [compiled]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        (compileExps trace compMap args).reverse (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.raise related, states⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      rw [compiled]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        (compileExps trace compMap args).reverse (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact post
  | @value sourceValues flatValues related =>
    have length := EvaluateProps.evaluateLengthFull source sourceNext sourceEnv args.reverse sourceValues sourceRun
    have bad : sourceValues.reverse.length ≠ 1 := by simpa [length] using badArity
    have rejected : doApp (sourceNext.refs, sourceNext.ffi) .envId sourceValues.reverse = none := by
      cases vals : sourceValues.reverse with
      | nil => simp [doApp, doAppNumericCore, doAppBasic]
      | cons first rest =>
        cases rest with
        | nil => simp [vals] at bad
        | cons second rest => simp [doApp, doAppNumericCore, doAppBasic]
    apply False.elim
    apply safe sourceNext
    change EvaluateHOL.evaluate source sourceEnv [.app .envId args] = _
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
    simp [getOpClass, rejected, EvaluateHOL.typeError]

/-- Malformed function applications propagate operand errors. -/
theorem localEnvBounded_opapp_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (args : List AstHOL.Exp) (badArity : args.length ≠ 2)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .opapp args) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv args.reverse ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .opapp args] = _
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
      simp only [compileExp, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        (compileExps trace compMap args).reverse (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      trivial
  | raise related =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      simp only [compileExp, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        (compileExps trace compMap args).reverse (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.raise related, states⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      simp only [compileExp, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        (compileExps trace compMap args).reverse (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact post
  | @value sourceValues flatValues related =>
    have length := EvaluateProps.evaluateLengthFull source sourceNext sourceEnv args.reverse sourceValues sourceRun
    have bad : sourceValues.reverse.length ≠ 2 := by simpa [length] using badArity
    have rejected : doOpApp sourceValues.reverse = none := by
      cases vals : sourceValues.reverse with
      | nil => simp [doOpApp]
      | cons first rest =>
        cases rest with
        | nil => simp [doOpApp]
        | cons second rest =>
          cases rest with
          | nil => simp [vals] at bad
          | cons third rest => simp [doOpApp]
    apply False.elim
    apply safe sourceNext
    change EvaluateHOL.evaluate source sourceEnv [.app .opapp args] = _
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
    simp [getOpClass, rejected, EvaluateHOL.typeError]

/-- Conversions reject every non-unary application after evaluating its
arguments. Argument errors are still propagated by the enclosing expression. -/
theorem localEnvBounded_conversion_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (fromType toType : PrimType) (args : List AstHOL.Exp) (badArity : args.length ≠ 1)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.fromTo fromType toType) args) := by
  apply localEnvBounded_rejectedSimple interp transform limit (.fromTo fromType toType) args rfl
    (by simp) (by simp) (by simp) _ each
  intro state values length
  have bad : values.length ≠ 1 := by simpa [length] using badArity
  cases values with
  | nil => cases fromType <;> cases toType <;> (try cases ‹WordSize›) <;> (try cases ‹WordSize›) <;>
      simp [doApp, doAppNumericCore]
  | cons first rest =>
    cases rest with
    | nil => simp at bad
    | cons second rest =>
      cases fromType <;> cases toType <;> (try cases ‹WordSize›) <;> (try cases ‹WordSize›) <;>
        simp [doApp, doAppNumericCore]

/-- Shifts reject non-unary argument lists after evaluating their operands. -/
theorem localEnvBounded_shift_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (size : WordSize) (shift : Shift) (amount : Nat) (args : List AstHOL.Exp) (badArity : args.length ≠ 1)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.shift size shift amount) args) := by
  apply localEnvBounded_rejectedSimple interp transform limit (.shift size shift amount) args rfl
    (by simp) (by simp) (by simp) _ each
  intro state values length
  have bad : values.length ≠ 1 := by simpa [length] using badArity
  cases values with
  | nil => cases size <;> simp [doApp, doAppNumericCore, doAppBasic]
  | cons first rest =>
    cases rest with
    | nil => simp at bad
    | cons second rest => cases size <;> simp [doApp, doAppNumericCore, doAppBasic]

/-- Equality and primitive tests reject non-binary argument lists after their
operands have been evaluated. -/
theorem localEnvBounded_comparison_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (test : Option (Test × PrimType)) (args : List AstHOL.Exp) (badArity : args.length ≠ 2)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit
      (.app (match test with | none => .equality | some (test, typ) => .test test typ) args) := by
  let op := match test with | none => Op.equality | some (test, typ) => Op.test test typ
  change LocalEnvBoundedIH (F := F) interp transform limit (.app op args)
  have simple : getOpClass op = .simple := by cases test <;> simp [op, getOpClass]
  have notEmpty : op ≠ .aallocEmpty := by cases test <;> simp [op]
  have notEval : op ≠ .eval := by cases test <;> simp [op]
  have notEnvId : op ≠ .envId := by cases test <;> simp [op]
  apply localEnvBounded_rejectedSimple interp transform limit op args simple notEmpty notEval notEnvId _ each
  intro state values length
  have bad : values.length ≠ 2 := by simpa [length] using badArity
  cases values with
  | nil => cases test <;> simp [op, doApp, doAppNumericCore, doAppBasic]
  | cons first rest =>
    cases rest with
    | nil => cases test <;> simp [op, doApp, doAppNumericCore, doAppBasic]
    | cons second rest =>
      cases rest with
      | nil => simp at bad
      | cons third rest => cases test <;> simp [op, doApp, doAppNumericCore, doAppBasic]

/-- Arithmetic operators take at least one and at most three operands. This
case preserves argument errors even when the operand count is outside that
range. More precise arities depend on the primitive type. -/
theorem localEnvBounded_arith_extremeArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (action : Arith) (typ : PrimType) (args : List AstHOL.Exp)
    (badArity : args.length = 0 ∨ 3 < args.length)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.arith action typ) args) := by
  apply localEnvBounded_rejectedSimple interp transform limit (.arith action typ) args rfl
    (by simp) (by simp) (by simp) _ each
  intro state values length
  have bad : values.length = 0 ∨ 3 < values.length := by simpa [length] using badArity
  cases values with
  | nil => cases typ <;> (try cases ‹WordSize›) <;> cases action <;>
      simp [doApp, doAppNumericCore, floatArith]
  | cons first rest =>
    cases rest with
    | nil => simp at bad
    | cons second rest =>
      cases rest with
      | nil => simp at bad
      | cons third rest =>
        cases rest with
        | nil => simp at bad
        | cons fourth rest =>
          cases typ <;> (try cases ‹WordSize›) <;> cases action <;>
            simp [doApp, doAppNumericCore, floatArith]

/-- Integer and word arithmetic reject every non-binary operand list. -/
theorem localEnvBounded_intWordArith_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (action : Arith) (size : Option WordSize) (args : List AstHOL.Exp) (badArity : args.length ≠ 2)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit
      (.app (.arith action (match size with | none => .intT | some w => .wordT w)) args) := by
  let typ := match size with | none => PrimType.intT | some w => PrimType.wordT w
  change LocalEnvBoundedIH (F := F) interp transform limit (.app (.arith action typ) args)
  apply localEnvBounded_rejectedSimple interp transform limit (.arith action typ) args rfl
    (by simp) (by simp) (by simp) _ each
  intro state values length
  have bad : values.length ≠ 2 := by simpa [length] using badArity
  cases values with
  | nil => cases size <;> simp [typ, doApp, doAppNumericCore]
  | cons first rest =>
    cases rest with
    | nil => cases size <;> simp [typ, doApp, doAppNumericCore]
    | cons second rest =>
      cases rest with
      | nil => simp at bad
      | cons third rest => cases size <;> simp [typ, doApp, doAppNumericCore]

/-- Boolean arithmetic rejects every non-unary operand list. -/
theorem localEnvBounded_boolArith_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (action : Arith) (args : List AstHOL.Exp) (badArity : args.length ≠ 1)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.arith action .boolT) args) := by
  apply localEnvBounded_rejectedSimple interp transform limit (.arith action .boolT) args rfl
    (by simp) (by simp) (by simp) _ each
  intro state values length
  have bad : values.length ≠ 1 := by simpa [length] using badArity
  cases values with
  | nil => cases action <;> simp [doApp, doAppNumericCore]
  | cons first rest =>
    cases rest with
    | nil => simp at bad
    | cons second rest => cases action <;> simp [doApp, doAppNumericCore]

/-- Only fused multiply-add accepts three floating-point operands. -/
theorem localEnvBounded_floatTernary_nonFma {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (action : Arith) (args : List AstHOL.Exp) (notFma : action ≠ .fma) (arity : args.length = 3)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.arith action .float64T) args) := by
  apply localEnvBounded_rejectedSimple interp transform limit (.arith action .float64T) args rfl
    (by simp) (by simp) (by simp) _ each
  intro state values length
  have count : values.length = 3 := by simpa [length] using arity
  cases values with
  | nil => simp at count
  | cons first rest =>
    cases rest with
    | nil => simp at count
    | cons second rest =>
      cases rest with
      | nil => simp at count
      | cons third rest =>
        cases rest with
        | cons fourth rest => simp at count
        | nil => cases action <;> simp [doApp, floatArith] at notFma ⊢

/-- Character and string arithmetic, and Boolean arithmetic other than
negation, reject every operand list after evaluating its expressions. -/
theorem localEnvBounded_arith_rejectedType {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (action : Arith) (typ : PrimType) (args : List AstHOL.Exp)
    (unsupported : typ = .charT ∨ typ = .strT ∨ (typ = .boolT ∧ action ≠ .not))
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.arith action typ) args) := by
  apply localEnvBounded_rejectedSimple interp transform limit (.arith action typ) args rfl
    (by simp) (by simp) (by simp) _ each
  intro state values _
  rcases unsupported with rfl | rfl | ⟨rfl, notNot⟩
  · simp [doApp, doAppNumericCore]
  · simp [doApp, doAppNumericCore]
  · cases action <;> simp [doApp, doAppNumericCore] at notNot ⊢

/-- The ordinary unary primitives used by references, strings, vectors, and
arrays. This predicate is bookkeeping for the factored simulation. -/
def UnaryBasicOp (op : Op) : Prop :=
  op = .opref ∨ op = .opderef ∨ op = .aw8length ∨ op = .implode ∨ op = .explode ∨
  op = .strlen ∨ op = .strcat ∨ op = .vfromList ∨ op = .vlength ∨ op = .alength

/-- Ordinary unary primitives reject operand lists of any other length. -/
theorem localEnvBounded_unaryBasic_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (op : Op) (args : List AstHOL.Exp) (unary : UnaryBasicOp op) (badArity : args.length ≠ 1)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app op args) := by
  rcases unary with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply localEnvBounded_rejectedSimple interp transform limit _ args rfl (by simp) (by simp) (by simp) _ each
  all_goals intro state values length
  all_goals have bad : values.length ≠ 1 := by simpa [length] using badArity
  all_goals cases values with
    | nil => simp [doApp, doAppNumericCore, doAppBasic]
    | cons first rest =>
      cases rest with
      | nil => simp at bad
      | cons second rest => simp [doApp, doAppNumericCore, doAppBasic]

/-- Ordinary binary reference, collection, and configuration primitives. -/
def BinaryBasicOp (op : Op) : Prop :=
  op = .opassign ∨ op = .listAppend ∨ op = .aw8alloc ∨ op = .aw8sub ∨ op = .aw8subUnsafe ∨
  op = .xorAw8StrUnsafe ∨ op = .strsub ∨ op = .vsub ∨ op = .vsubUnsafe ∨ op = .aalloc ∨
  op = .asub ∨ op = .asubUnsafe ∨ op = .configGC

/-- Ordinary binary primitives reject operand lists of any other length. -/
theorem localEnvBounded_binaryBasic_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (op : Op) (args : List AstHOL.Exp) (binary : BinaryBasicOp op) (badArity : args.length ≠ 2)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app op args) := by
  rcases binary with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply localEnvBounded_rejectedSimple interp transform limit _ args rfl (by simp) (by simp) (by simp) _ each
  all_goals intro state values length
  all_goals have bad : values.length ≠ 2 := by simpa [length] using badArity
  all_goals cases values with
    | nil => simp [doApp, doAppNumericCore, doAppBasic]
    | cons first rest =>
      cases rest with
      | nil => simp [doApp, doAppNumericCore, doAppBasic]
      | cons second rest =>
        cases rest with
        | nil => simp at bad
        | cons third rest => simp [doApp, doAppNumericCore, doAppBasic]

/-- Ordinary ternary update and slicing primitives. -/
def TernaryBasicOp (op : Op) : Prop :=
  op = .aupdate ∨ op = .aupdateUnsafe ∨ op = .aw8update ∨ op = .aw8updateUnsafe ∨
  op = .copyStrStr ∨ op = .copyAw8Str

/-- Ordinary ternary primitives reject operand lists of any other length. -/
theorem localEnvBounded_ternaryBasic_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (op : Op) (args : List AstHOL.Exp) (ternary : TernaryBasicOp op) (badArity : args.length ≠ 3)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app op args) := by
  rcases ternary with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply localEnvBounded_rejectedSimple interp transform limit _ args rfl (by simp) (by simp) (by simp) _ each
  all_goals intro state values length
  all_goals have bad : values.length ≠ 3 := by simpa [length] using badArity
  all_goals cases values with
    | nil => simp [doApp, doAppNumericCore, doAppBasic]
    | cons first rest =>
      cases rest with
      | nil => simp [doApp, doAppNumericCore, doAppBasic]
      | cons second rest =>
        cases rest with
        | nil => simp [doApp, doAppNumericCore, doAppBasic]
        | cons third rest =>
          cases rest with
          | nil => simp at bad
          | cons fourth rest => simp [doApp, doAppNumericCore, doAppBasic]

/-- The two five-operand byte-copy primitives. -/
def FiveArgBasicOp (op : Op) : Prop := op = .copyStrAw8 ∨ op = .copyAw8Aw8

/-- Five-operand byte copies reject operand lists of any other length. -/
theorem localEnvBounded_fiveArgBasic_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (op : Op) (args : List AstHOL.Exp) (copy : FiveArgBasicOp op) (badArity : args.length ≠ 5)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app op args) := by
  rcases copy with rfl | rfl
  all_goals apply localEnvBounded_rejectedSimple interp transform limit _ args rfl (by simp) (by simp) (by simp) _ each
  all_goals intro state values length
  all_goals have bad : values.length ≠ 5 := by simpa [length] using badArity
  all_goals cases values with
    | nil => simp [doApp, doAppNumericCore, doAppBasic]
    | cons first rest =>
      cases rest with
      | nil => simp [doApp, doAppNumericCore, doAppBasic]
      | cons second rest =>
        cases rest with
        | nil => simp [doApp, doAppNumericCore, doAppBasic]
        | cons third rest =>
          cases rest with
          | nil => simp [doApp, doAppNumericCore, doAppBasic]
          | cons fourth rest =>
            cases rest with
            | nil => simp [doApp, doAppNumericCore, doAppBasic]
            | cons fifth rest =>
              cases rest with
              | nil => simp at bad
              | cons sixth rest => simp [doApp, doAppNumericCore, doAppBasic]

/-- Foreign calls reject non-binary operand lists after evaluating them. -/
theorem localEnvBounded_ffi_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (name : Basis.Pure.MlString.MlString) (args : List AstHOL.Exp) (badArity : args.length ≠ 2)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.ffi name) args) := by
  apply localEnvBounded_rejectedSimple interp transform limit (.ffi name) args rfl
    (by simp) (by simp) (by simp) _ each
  intro state values length
  have bad : values.length ≠ 2 := by simpa [length] using badArity
  cases values with
  | nil => simp [doApp, doAppNumericCore, doAppBasic]
  | cons first rest =>
    cases rest with
    | nil => simp [doApp, doAppNumericCore, doAppBasic]
    | cons second rest =>
      cases rest with
      | nil => simp at bad
      | cons third rest => simp [doApp, doAppNumericCore, doAppBasic]

/-- Thunk allocation rejects non-unary operand lists. -/
theorem localEnvBounded_allocThunk_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (mode : ThunkMode) (args : List AstHOL.Exp) (badArity : args.length ≠ 1)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.thunkOp (.allocThunk mode)) args) := by
  apply localEnvBounded_rejectedSimple interp transform limit (.thunkOp (.allocThunk mode)) args rfl
    (by simp) (by simp) (by simp) _ each
  intro state values length
  have bad : values.length ≠ 1 := by simpa [length] using badArity
  cases values with
  | nil => simp [doApp, doAppNumericCore, doAppBasic, thunkOp]
  | cons first rest =>
    cases rest with
    | nil => simp at bad
    | cons second rest => simp [doApp, doAppNumericCore, doAppBasic, thunkOp]

/-- Thunk update rejects non-binary operand lists. -/
theorem localEnvBounded_updateThunk_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (mode : ThunkMode) (args : List AstHOL.Exp) (badArity : args.length ≠ 2)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.thunkOp (.updateThunk mode)) args) := by
  apply localEnvBounded_rejectedSimple interp transform limit (.thunkOp (.updateThunk mode)) args rfl
    (by simp) (by simp) (by simp) _ each
  intro state values length
  have bad : values.length ≠ 2 := by simpa [length] using badArity
  cases values with
  | nil => simp [doApp, doAppNumericCore, doAppBasic, thunkOp]
  | cons first rest =>
    cases rest with
    | nil => simp [doApp, doAppNumericCore, doAppBasic, thunkOp]
    | cons second rest =>
      cases rest with
      | nil => simp at bad
      | cons third rest => simp [doApp, doAppNumericCore, doAppBasic, thunkOp]

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



/-- Compose test operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_test {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (test : Test) (typ : PrimType) (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.test test typ) [left, right]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by simp) (by simp) (by simp) (by simp [getOpClass])
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> assumption

/-- Compose equality operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_equality {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .equality [left, right]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by simp) (by simp) (by simp) (by simp [getOpClass])
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> assumption

/-- Compose integerArith operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_integerArith {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (action : Arith) (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.arith action .intT) [left, right]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by simp) (by simp) (by simp) (by simp [getOpClass])
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> assumption

/-- Compose word8Arith operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_word8Arith {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (action : Arith) (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.arith action (.wordT .w8)) [left, right]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by simp) (by simp) (by simp) (by simp [getOpClass])
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> assumption

/-- Compose word64Arith operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_word64Arith {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (action : Arith) (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.arith action (.wordT .w64)) [left, right]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by simp) (by simp) (by simp) (by simp [getOpClass])
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> assumption

/-- Binary floating-point arithmetic preserves the factored simulation. -/
theorem localEnvBounded_floatBinary {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (action : Arith) (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.arith action .float64T) [left, right]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by simp) (by simp) (by simp) (by simp [getOpClass])
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> assumption

/-- Word8 shifts compose a growing operand simulation in a local environment. -/
theorem localEnvBounded_word8Shift {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp) (shift : Shift) (amount : Nat)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.shift .w8 shift amount) [body]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by simp) (by simp) (by simp) (by simp [getOpClass])
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst expr
  assumption

/-- Word64 shifts compose a growing operand simulation in a local environment. -/
theorem localEnvBounded_word64Shift {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp) (shift : Shift) (amount : Nat)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.shift .w64 shift amount) [body]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by simp) (by simp) (by simp) (by simp [getOpClass])
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst expr
  assumption

/-- Primitive conversions compose a growing operand simulation in a local environment. -/
theorem localEnvBounded_conversion {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp) (fromType toType : PrimType)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.fromTo fromType toType) [body]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by simp) (by simp) (by simp) (by simp [getOpClass])
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst expr
  assumption

/-- Unary floating-point operations compose a bounded operand simulation. -/
theorem localEnvBounded_floatUnary {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp) (action : Arith)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.arith action .float64T) [body]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by simp) (by simp) (by simp) (by simp [getOpClass])
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst expr
  assumption

/-- Boolean negation composes a bounded operand simulation. -/
theorem localEnvBounded_booleanNot {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.arith .not .boolT) [body]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by simp) (by simp) (by simp) (by simp [getOpClass])
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst expr
  assumption

/-- Reference dereferences compose a growing operand simulation in a local environment. -/
theorem localEnvBounded_opderef {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .opderef [body]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by simp) (by simp) (by simp) (by simp [getOpClass])
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst expr
  assumption

/-- Reference allocation compose a growing operand simulation in a local environment. -/
theorem localEnvBounded_opref {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .opref [body]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by simp) (by simp) (by simp) (by simp [getOpClass])
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst expr
  assumption

/-- Compose reference assignment operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_opassign {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .opassign [left, right]) := by
  apply localEnvBounded_simpleApp interp transform limit _ (by simp) (by simp) (by simp) (by simp [getOpClass])
  intro expr member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> assumption

end Flapjack.Compiler.Backend.SourceToFlat
