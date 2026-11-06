import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateBoundPure
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateApply

/-! Primitive comparisons of state-preserving local expressions over the
preliminary factored source-to-flat relations. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- A comparison of covered local expressions preserves the growing step,
including right-to-left evaluation and rejected primitive operands. -/
theorem localExpressionStep_boundTest {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (baseEnv : SemEnv Value)
    (trace : List VarN) (baseMap : Environment) (gen : EnvironmentGenerationStore)
    (name : VarN) (value : Value) (flatValue : FlatSem.Value) (test : Test) (typ : PrimType)
    (left right : AstHOL.Exp) (leftCovered : BoundPureExpression name left)
    (rightCovered : BoundPureExpression name right) (relatedValue : ValueRel genv value flatValue)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState)
    (safe : ∀ last, EvaluateHOL.evaluate source { baseEnv with v := nsBind name value baseEnv.v }
      [.app (.test test typ) [left, right]] ≠ (last, .err (.abort .typeError))) :
    LocalExpressionStep interp transform genv start finish other source flat
      { baseEnv with v := nsBind name value baseEnv.v } ⟨[(name, flatValue)]⟩ trace
      { baseMap with v := nsBind name (.localName .none name) baseMap.v } gen
      (.app (.test test typ) [left, right]) := by
  let sourceEnv := { baseEnv with v := nsBind name value baseEnv.v }
  let compMap := { baseMap with v := nsBind name (.localName .none name) baseMap.v }
  let flatEnv : FlatSem.Environment FlatSem.Value := ⟨[(name, flatValue)]⟩
  obtain ⟨nextGenv, argsSim, post⟩ := boundPure_pairStep interp transform genv start finish other source flat
    baseEnv trace baseMap gen name value flatValue left right leftCovered rightCovered relatedValue invariant generation
  have argsSimCopy := argsSim
  unfold ExprListSim at argsSim
  simp only [compileExps] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [right, left] = sourceResult at argsSim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap right, compileExp trace compMap left] = flatResult at argsSim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := argsSim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      trivial
  | raise valueRel =>
    obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
    refine ⟨nextGenv, exprSim_test nextGenv compMap trace sourceEnv flatEnv source flat left right test typ
      nextInvariant.1 argsSimCopy safe, ?_⟩
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
    simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
    rw [FlatSem.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(FlatSem.fixClock_evaluations flatEnv flat
      [compileExp trace compMap right, compileExp trace compMap left]
      (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
    exact ⟨growth, nextInvariant, nextGeneration, forward⟩
  | @value sourceValues flatValues valuesRel =>
    have length := EvaluateProps.evaluateLengthFull source nextSource sourceEnv [right, left] sourceValues sourceRun
    have two : ∃ v p, sourceValues = [v, p] := by
      cases sourceValues with
      | nil => simp at length
      | cons v tail =>
        cases tail with
        | nil => simp at length
        | cons p rest =>
          cases rest with
          | nil => exact ⟨v, p, rfl⟩
          | cons q rest => simp at length
    obtain ⟨sourceRight, sourceLeft, rfl⟩ := two
    cases valuesRel with
    | cons rightRel tail =>
      cases tail with
      | cons leftRel tail =>
        cases tail with
        | nil =>
          rename_i flatRight flatLeft
          obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
          cases comparison : SemanticPrimitivesHOL.doTest test typ sourceLeft sourceRight with
          | typeError =>
            apply False.elim
            apply safe nextSource
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp [getOpClass, doApp, comparison, EvaluateHOL.typeError]
          | val b =>
            have flatComparison := doTest_related nextGenv nextInvariant.1 test typ sourceLeft sourceRight
              flatLeft flatRight b leftRel rightRel comparison
            refine ⟨nextGenv, exprSim_test nextGenv compMap trace sourceEnv flatEnv source flat left right test typ
              nextInvariant.1 argsSimCopy safe, ?_⟩
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
            rw [FlatSem.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(FlatSem.fixClock_evaluations flatEnv flat
              [compileExp trace compMap right, compileExp trace compMap left]
              (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
            simpa [getOpClass, doApp, comparison, astOpToFlatOp, FlatSem.applyResult,
              FlatSem.doApp, FlatSem.doAppNumeric, flatComparison, EvaluateHOL.listResult] using
              And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))


/-- Equality of covered local expressions preserves the growing step,
including right-to-left evaluation and rejected primitive operands. -/
theorem localExpressionStep_boundEquality {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (baseEnv : SemEnv Value)
    (trace : List VarN) (baseMap : Environment) (gen : EnvironmentGenerationStore)
    (name : VarN) (value : Value) (flatValue : FlatSem.Value)
    (left right : AstHOL.Exp) (leftCovered : BoundPureExpression name left)
    (rightCovered : BoundPureExpression name right) (relatedValue : ValueRel genv value flatValue)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState)
    (safe : ∀ last, EvaluateHOL.evaluate source { baseEnv with v := nsBind name value baseEnv.v }
      [.app .equality [left, right]] ≠ (last, .err (.abort .typeError))) :
    LocalExpressionStep interp transform genv start finish other source flat
      { baseEnv with v := nsBind name value baseEnv.v } ⟨[(name, flatValue)]⟩ trace
      { baseMap with v := nsBind name (.localName .none name) baseMap.v } gen
      (.app .equality [left, right]) := by
  let sourceEnv := { baseEnv with v := nsBind name value baseEnv.v }
  let compMap := { baseMap with v := nsBind name (.localName .none name) baseMap.v }
  let flatEnv : FlatSem.Environment FlatSem.Value := ⟨[(name, flatValue)]⟩
  obtain ⟨nextGenv, argsSim, post⟩ := boundPure_pairStep interp transform genv start finish other source flat
    baseEnv trace baseMap gen name value flatValue left right leftCovered rightCovered relatedValue invariant generation
  have argsSimCopy := argsSim
  unfold ExprListSim at argsSim
  simp only [compileExps] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [right, left] = sourceResult at argsSim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap right, compileExp trace compMap left] = flatResult at argsSim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := argsSim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      trivial
  | raise valueRel =>
    obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
    refine ⟨nextGenv, exprSim_equality nextGenv compMap trace sourceEnv flatEnv source flat left right
      nextInvariant.1 argsSimCopy safe, ?_⟩
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
    simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
    rw [FlatSem.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(FlatSem.fixClock_evaluations flatEnv flat
      [compileExp trace compMap right, compileExp trace compMap left]
      (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
    exact ⟨growth, nextInvariant, nextGeneration, forward⟩
  | @value sourceValues flatValues valuesRel =>
    have length := EvaluateProps.evaluateLengthFull source nextSource sourceEnv [right, left] sourceValues sourceRun
    have two : ∃ v p, sourceValues = [v, p] := by
      cases sourceValues with
      | nil => simp at length
      | cons v tail =>
        cases tail with
        | nil => simp at length
        | cons p rest =>
          cases rest with
          | nil => exact ⟨v, p, rfl⟩
          | cons q rest => simp at length
    obtain ⟨sourceRight, sourceLeft, rfl⟩ := two
    cases valuesRel with
    | cons rightRel tail =>
      cases tail with
      | cons leftRel tail =>
        cases tail with
        | nil =>
          rename_i flatRight flatLeft
          obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
          cases comparison : SemanticPrimitivesHOL.doEq sourceLeft sourceRight with
          | typeError =>
            apply False.elim
            apply safe nextSource
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp [getOpClass, doApp, doAppNumericCore, doAppBasic, comparison, EvaluateHOL.typeError]
          | val b =>
            have flatComparison := equality_preserved nextGenv nextInvariant.1 sourceLeft sourceRight
              flatLeft flatRight leftRel rightRel
            refine ⟨nextGenv, exprSim_equality nextGenv compMap trace sourceEnv flatEnv source flat left right
              nextInvariant.1 argsSimCopy safe, ?_⟩
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
            rw [FlatSem.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(FlatSem.fixClock_evaluations flatEnv flat
              [compileExp trace compMap right, compileExp trace compMap left]
              (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
            simpa [getOpClass, doApp, doAppNumericCore, doAppBasic, comparison, astOpToFlatOp, FlatSem.applyResult,
              FlatSem.doApp, FlatSem.doAppNumeric, flatComparison, EvaluateHOL.listResult] using
              And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))


/-- Integer arithmetic on covered local expressions preserves the growing step,
including right-to-left evaluation and rejected primitive operands. -/
theorem localExpressionStep_boundIntegerArith {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (baseEnv : SemEnv Value)
    (trace : List VarN) (baseMap : Environment) (gen : EnvironmentGenerationStore)
    (name : VarN) (value : Value) (flatValue : FlatSem.Value) (action : Arith)
    (left right : AstHOL.Exp) (leftCovered : BoundPureExpression name left)
    (rightCovered : BoundPureExpression name right) (relatedValue : ValueRel genv value flatValue)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState)
    (safe : ∀ last, EvaluateHOL.evaluate source { baseEnv with v := nsBind name value baseEnv.v }
      [.app (.arith action .intT) [left, right]] ≠ (last, .err (.abort .typeError))) :
    LocalExpressionStep interp transform genv start finish other source flat
      { baseEnv with v := nsBind name value baseEnv.v } ⟨[(name, flatValue)]⟩ trace
      { baseMap with v := nsBind name (.localName .none name) baseMap.v } gen
      (.app (.arith action .intT) [left, right]) := by
  let sourceEnv := { baseEnv with v := nsBind name value baseEnv.v }
  let compMap := { baseMap with v := nsBind name (.localName .none name) baseMap.v }
  let flatEnv : FlatSem.Environment FlatSem.Value := ⟨[(name, flatValue)]⟩
  obtain ⟨nextGenv, argsSim, post⟩ := boundPure_pairStep interp transform genv start finish other source flat
    baseEnv trace baseMap gen name value flatValue left right leftCovered rightCovered relatedValue invariant generation
  have argsSimCopy := argsSim
  unfold ExprListSim at argsSim
  simp only [compileExps] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [right, left] = sourceResult at argsSim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap right, compileExp trace compMap left] = flatResult at argsSim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := argsSim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      trivial
  | raise valueRel =>
    obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
    refine ⟨nextGenv, exprSim_integerArith nextGenv compMap trace sourceEnv flatEnv source flat left right action
      nextInvariant.1 argsSimCopy safe, ?_⟩
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
    simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
    rw [FlatSem.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(FlatSem.fixClock_evaluations flatEnv flat
      [compileExp trace compMap right, compileExp trace compMap left]
      (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
    exact ⟨growth, nextInvariant, nextGeneration, forward⟩
  | @value sourceValues flatValues valuesRel =>
    have length := EvaluateProps.evaluateLengthFull source nextSource sourceEnv [right, left] sourceValues sourceRun
    have two : ∃ v p, sourceValues = [v, p] := by
      cases sourceValues with
      | nil => simp at length
      | cons v tail =>
        cases tail with
        | nil => simp at length
        | cons p rest =>
          cases rest with
          | nil => exact ⟨v, p, rfl⟩
          | cons q rest => simp at length
    obtain ⟨sourceRight, sourceLeft, rfl⟩ := two
    cases valuesRel with
    | cons rightRel tail =>
      cases tail with
      | cons leftRel tail =>
        cases tail with
        | nil =>
          rename_i flatRight flatLeft
          obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
          have successful : doApp (nextSource.refs, nextSource.ffi) (.arith action .intT)
              [sourceLeft, sourceRight] ≠ none := by
            intro failed
            apply safe nextSource
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp [getOpClass, failed, EvaluateHOL.typeError]
          obtain ⟨leftInt, rightInt, operands⟩ := integerArith_operands nextSource action [sourceLeft, sourceRight] successful
          simp only [List.cons.injEq] at operands
          obtain ⟨rfl, rfl, _⟩ := operands
          have flatLeftEq := (valueRel_literal_iff nextGenv (.intLit leftInt) flatLeft).mp leftRel
          have flatRightEq := (valueRel_literal_iff nextGenv (.intLit rightInt) flatRight).mp rightRel
          subst flatLeft
          subst flatRight
          have primitive := integerArith_related nextGenv nextInvariant.1 nextSource nextFlat action leftInt rightInt
          cases sourceApp : doApp (nextSource.refs, nextSource.ffi) (.arith action .intT)
              [.litv (.intLit leftInt), .litv (.intLit rightInt)] with
          | none => exact (successful sourceApp).elim
          | some sourceOut =>
            cases sourceOut with
            | mk store sourceResult =>
              cases store with
              | mk refs ffi =>
                cases flatApp : FlatSem.doAppNumeric nextFlat (.arith action .intT)
                    [.litv (.intLit leftInt), .litv (.intLit rightInt)] with
                | none => simp [sourceApp, flatApp] at primitive
                | some flatOut =>
                  cases flatOut with
                  | none => simp [sourceApp, flatApp] at primitive
                  | some flatOut =>
                    cases flatOut with
                    | mk flatAfter flatResult =>
                      simp only [sourceApp, flatApp] at primitive
                      obtain ⟨rfl, rfl, rfl, resultRel⟩ := primitive
                      refine ⟨nextGenv, exprSim_integerArith nextGenv compMap trace sourceEnv flatEnv source flat
                        left right action nextInvariant.1 argsSimCopy safe, ?_⟩
                      rw [EvaluateHOL.evaluate]
                      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
                      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                      rw [FlatSem.evaluate]
                      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                      rw [(FlatSem.fixClock_evaluations flatEnv flat
                        [compileExp trace compMap right, compileExp trace compMap left]
                        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
                      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                        getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp, flatApp]
                      cases resultRel with
                      | value valueRel =>
                        simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant
                          (And.intro nextGeneration forward))
                      | raise valueRel =>
                        simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant
                          (And.intro nextGeneration forward))
                      | abort error => simp [EvaluateHOL.listResult]

/-- A named binding with a primitive comparison of covered local operands
satisfies the preliminary declaration-expression induction hypothesis. -/
theorem factoredExpressionIH_let_named_test {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (first : AstHOL.Exp) (test : Test) (typ : PrimType) (left right : AstHOL.Exp)
    (leftCovered : BoundPureExpression name left) (rightCovered : BoundPureExpression name right)
    (firstIH : FactoredExpressionIH (F := F) interp transform first) :
    FactoredExpressionIH (F := F) interp transform (.let_ (some name) first (.app (.test test typ) [left, right])) := by
  apply factoredExpressionIH_let_named_of_local interp transform name first _ firstIH
  intro genv start finish other source flat sourceEnv trace compMap gen value flatValue related _ invariant generation safe
  exact localExpressionStep_boundTest interp transform genv start finish other source flat sourceEnv trace compMap gen
    name value flatValue test typ left right leftCovered rightCovered related invariant generation safe

/-- A named binding with equality over covered local operands satisfies the
preliminary declaration-expression induction hypothesis. -/
theorem factoredExpressionIH_let_named_equality {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (first left right : AstHOL.Exp)
    (leftCovered : BoundPureExpression name left) (rightCovered : BoundPureExpression name right)
    (firstIH : FactoredExpressionIH (F := F) interp transform first) :
    FactoredExpressionIH (F := F) interp transform (.let_ (some name) first (.app .equality [left, right])) := by
  apply factoredExpressionIH_let_named_of_local interp transform name first _ firstIH
  intro genv start finish other source flat sourceEnv trace compMap gen value flatValue related _ invariant generation safe
  exact localExpressionStep_boundEquality interp transform genv start finish other source flat sourceEnv trace compMap gen
    name value flatValue left right leftCovered rightCovered related invariant generation safe

/-- Named bindings with integer arithmetic over covered local operands
satisfy the preliminary declaration-expression induction hypothesis. -/
theorem factoredExpressionIH_let_named_integerArith {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (first : AstHOL.Exp) (action : Arith) (left right : AstHOL.Exp)
    (leftCovered : BoundPureExpression name left) (rightCovered : BoundPureExpression name right)
    (firstIH : FactoredExpressionIH (F := F) interp transform first) :
    FactoredExpressionIH (F := F) interp transform
      (.let_ (some name) first (.app (.arith action .intT) [left, right])) := by
  apply factoredExpressionIH_let_named_of_local interp transform name first _ firstIH
  intro genv start finish other source flat sourceEnv trace compMap gen value flatValue related _ invariant generation safe
  exact localExpressionStep_boundIntegerArith interp transform genv start finish other source flat sourceEnv trace compMap gen
    name value flatValue action left right leftCovered rightCovered related invariant generation safe

end Flapjack.Compiler.Backend.SourceToFlat
