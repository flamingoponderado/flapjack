module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.DoApp
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBounded
public import Flapjack.Compiler.Backend.FlatProps.DoAppState

@[expose] public section

namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- The generic simple-operator step used by the bounded induction. This is
Flapjack infrastructure corresponding to the `do_app` portion of HOL's
`compile_correct` application case. -/
theorem localEnvBounded_simpleApp {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (op : Op) (notEmpty : op ≠ .aallocEmpty) (notEval : op ≠ .eval)
    (notEnvId : op ≠ .envId) (simple : getOpClass op = .simple) (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app op args) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  change LocalExpressionStep interp transform genv start finish other source flat sourceEnv flatEnv trace compMap gen
    (.app op args)
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv args.reverse ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app op args] = _
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform limit args.reverse
    (fun expr member => each expr (List.mem_reverse.mp member)) genv start finish other source flat
    baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
  unfold ExprListSim at argsSim
  rw [compileExps_reverse] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv args.reverse = sourceResult at argsSim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat (compileExps trace compMap args).reverse = flatResult at argsSim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := argsSim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      simp only [compileExp, notEmpty, notEval, notEnvId, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat (compileExps trace compMap args).reverse
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      trivial
  | raise valueRel =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      simp only [compileExp, notEmpty, notEval, notEnvId, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat (compileExps trace compMap args).reverse
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.raise valueRel, states⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      simp only [compileExp, notEmpty, notEval, notEnvId, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat (compileExps trace compMap args).reverse
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact post
  | @value sourceValues flatValues valuesRel =>
    obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
    have flatDispatch : astOpToFlatOp op ≠ .src .opapp ∧
        astOpToFlatOp op ≠ .src .eval ∧
        astOpToFlatOp op ≠ .src (.thunkOp .forceThunk) := by
      cases op <;> simp_all [astOpToFlatOp, getOpClass]
    cases sourceApp : doApp (nextSource.refs, nextSource.ffi) op sourceValues.reverse with
    | none =>
      exfalso
      apply safe nextSource
      change EvaluateHOL.evaluate source sourceEnv [.app op args] = _
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      simp [simple, sourceApp, EvaluateHOL.typeError]
    | some pair =>
      obtain ⟨⟨sourceRefs, sourceFfi⟩, sourceResult⟩ := pair
      obtain ⟨nonempty, stores, clocks, ffi⟩ := (stateRel_iff nextGenv nextSource nextFlat).mp states
      obtain ⟨flatResult, flatLast, nextStores, nextNonempty, nextFfi, globals, reserved, resultRel, flatApp⟩ :=
        doApp_correct nextGenv (nextSource.refs, nextSource.ffi) (sourceRefs, sourceFfi) op
          sourceValues.reverse sourceResult nextFlat flatValues.reverse
          ⟨sourceApp, stores, nonempty, List.rel_reverse valuesRel, ffi, nextInvariant.1, notEmpty, notEnvId⟩
      have flatClock := (FlatSem.doApp_const nextFlat _ _ flatLast _ flatApp).symm
      have flatConfig := FlatProps.doApp_stateUnchanged () nextFlat _ _ flatLast _ flatApp
      have flatShape : flatLast = { nextFlat with refs := flatLast.refs, ffi := sourceFfi } := by
        cases nextFlat
        cases flatLast
        simp_all
      have afterRel0 : StateRel nextGenv { nextSource with refs := sourceRefs, ffi := sourceFfi }
          flatLast := .intro _ _ nextNonempty nextStores (clocks.trans flatClock.symm) nextFfi
      have afterRel : StateRel nextGenv { nextSource with refs := sourceRefs, ffi := sourceFfi }
          { nextFlat with refs := flatLast.refs, ffi := sourceFfi } := by
        simpa only [← flatShape] using afterRel0
      have afterInv := factoredInvariant_changeStores interp transform gen nextGenv (start, finish, other)
        nextSource nextFlat sourceRefs flatLast.refs sourceFfi sourceFfi nextInvariant afterRel reserved.symm
      cases resultRel with
      | value valueRel =>
        refine ⟨nextGenv, ?_, ?_⟩
        · unfold ExprSim
          rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
          simp only [compileExp, notEmpty, notEval, notEnvId, ↓reduceIte]
          rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat (compileExps trace compMap args).reverse
            (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
          simp only [simple, sourceApp, EvaluateHOL.listResult]
          split
          · rename_i h; exact False.elim (flatDispatch.1 h)
          · rename_i h; exact False.elim (flatDispatch.2.1 h)
          · rename_i h; exact False.elim (flatDispatch.2.2 h)
          · simp [FlatSem.applyResult, flatApp]
            exact ⟨.value (.cons valueRel .nil), afterRel0⟩
        · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
          simp only [compileExp, notEmpty, notEval, notEnvId, ↓reduceIte]
          rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat (compileExps trace compMap args).reverse
            (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
          simp only [simple, sourceApp, EvaluateHOL.listResult]
          split
          · rename_i h; exact False.elim (flatDispatch.1 h)
          · rename_i h; exact False.elim (flatDispatch.2.1 h)
          · rename_i h; exact False.elim (flatDispatch.2.2 h)
          · simp only [FlatSem.applyResult, flatApp]
            simpa only [← flatShape] using And.intro growth (And.intro afterInv (And.intro nextGeneration forward))
      | raise valueRel =>
        refine ⟨nextGenv, ?_, ?_⟩
        · unfold ExprSim
          rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
          simp only [compileExp, notEmpty, notEval, notEnvId, ↓reduceIte]
          rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat (compileExps trace compMap args).reverse
            (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
          simp only [simple, sourceApp, EvaluateHOL.listResult]
          split
          · rename_i h; exact False.elim (flatDispatch.1 h)
          · rename_i h; exact False.elim (flatDispatch.2.1 h)
          · rename_i h; exact False.elim (flatDispatch.2.2 h)
          · simp [FlatSem.applyResult, flatApp]
            exact ⟨.raise valueRel, afterRel0⟩
        · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
          simp only [compileExp, notEmpty, notEval, notEnvId, ↓reduceIte]
          rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat (compileExps trace compMap args).reverse
            (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
          simp only [simple, sourceApp, EvaluateHOL.listResult]
          split
          · rename_i h; exact False.elim (flatDispatch.1 h)
          · rename_i h; exact False.elim (flatDispatch.2.1 h)
          · rename_i h; exact False.elim (flatDispatch.2.2 h)
          · simp only [FlatSem.applyResult, flatApp]
            simpa only [← flatShape] using And.intro growth (And.intro afterInv (And.intro nextGeneration forward))
      | abort error =>
        refine ⟨nextGenv, ?_, ?_⟩
        · unfold ExprSim
          rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
          simp only [compileExp, notEmpty, notEval, notEnvId, ↓reduceIte]
          rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat (compileExps trace compMap args).reverse
            (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
          simp only [simple, sourceApp, EvaluateHOL.listResult]
          split
          · rename_i h; exact False.elim (flatDispatch.1 h)
          · rename_i h; exact False.elim (flatDispatch.2.1 h)
          · rename_i h; exact False.elim (flatDispatch.2.2 h)
          · simp [FlatSem.applyResult, flatApp]
            exact ⟨.abort error, afterRel0⟩
        · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
          simp [simple, sourceApp, EvaluateHOL.listResult]

end Flapjack.Compiler.Backend.SourceToFlat
