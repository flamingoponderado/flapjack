import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateBoundIf

/-! Growing local operand lists, over preliminary factored relations. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

private theorem sourcePair {F : Type} (source : State F) (env : SemEnv Value) (first second : AstHOL.Exp) :
    EvaluateHOL.evaluate source env [first, second] =
      let head := EvaluateHOL.evaluate source env [first]
      match head.2 with
      | .err error => (head.1, .err error)
      | .val values =>
        let tail := EvaluateHOL.evaluate head.1 env [second]
        match tail.2 with
        | .err error => (tail.1, .err error)
        | .val values' => (tail.1, .val (EvaluateHOL.headValue values :: values')) := by
  rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source env [first] []).1]
  rfl

private theorem flatPair {C F : Type} (flat : FlatSem.State C F) (env : FlatSem.Environment FlatSem.Value)
    (trace : List VarN) (compMap : Environment) (first second : AstHOL.Exp) :
    FlatSem.evaluate env flat (compileExps trace compMap [first, second]) =
      let head := FlatSem.evaluate env flat [compileExp trace compMap first]
      match head.2 with
      | .err error => (head.1, .err error)
      | .val values =>
        let tail := FlatSem.evaluate env head.1 (compileExps trace compMap [second])
        match tail.2 with
        | .err error => (tail.1, .err error)
        | .val values' => (tail.1, .val (@Flapjack.holHd FlatSem.Value ⟨FlatSem.unitValue⟩ values :: values')) := by
  simp only [compileExps]
  rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations env flat
    [compileExp trace compMap first] (FlatLang.Exp.lit .none (.intLit 0)) []).1]
  rfl

/-- Sequentially compose two local expression hypotheses. Their order is
explicit; primitive operations supply the source's reversed operand order. -/
theorem boundLocal_pairStep {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (baseEnv : SemEnv Value)
    (trace : List VarN) (baseMap : Environment) (gen : EnvironmentGenerationStore)
    (name : VarN) (value : Value) (flatValue : FlatSem.Value) (first second : AstHOL.Exp)
    (firstIH : BoundLocalIH (F := F) interp transform name first)
    (secondIH : BoundLocalIH (F := F) interp transform name second)
    (related : ValueRel genv value flatValue)
    (envInv : GlobalEnvInv genv baseMap (fun _ => False) baseEnv)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState)
    (safe : ∀ last, EvaluateHOL.evaluate source { baseEnv with v := nsBind name value baseEnv.v } [first, second] ≠
      (last, .err (.abort .typeError))) :
    let sourceEnv := { baseEnv with v := nsBind name value baseEnv.v }
    let compMap := { baseMap with v := nsBind name (.localName .none name) baseMap.v }
    let flatEnv : FlatSem.Environment FlatSem.Value := ⟨[(name, flatValue)]⟩
    ∃ nextGenv, ExprListSim nextGenv compMap trace sourceEnv flatEnv source flat [first, second] ∧
      match (EvaluateHOL.evaluate source sourceEnv [first, second]).2 with
      | .err (.abort _) => True
      | _ => GlobalGrowth genv nextGenv ∧
          factoredInvariant interp transform gen nextGenv (start, finish, other)
            (EvaluateHOL.evaluate source sourceEnv [first, second]).1
            (FlatSem.evaluate flatEnv flat (compileExps trace compMap [first, second])).1 ∧
          envGenRel gen (EvaluateHOL.evaluate source sourceEnv [first, second]).1.evalState ∧
          oracForwardRel interp source.evalState (EvaluateHOL.evaluate source sourceEnv [first, second]).1.evalState := by
  let sourceEnv := { baseEnv with v := nsBind name value baseEnv.v }
  let compMap := { baseMap with v := nsBind name (.localName .none name) baseMap.v }
  let flatEnv : FlatSem.Environment FlatSem.Value := ⟨[(name, flatValue)]⟩
  change ∃ nextGenv, ExprListSim nextGenv compMap trace sourceEnv flatEnv source flat [first, second] ∧
    match (EvaluateHOL.evaluate source sourceEnv [first, second]).2 with
    | .err (.abort _) => True
    | _ => GlobalGrowth genv nextGenv ∧
        factoredInvariant interp transform gen nextGenv (start, finish, other)
          (EvaluateHOL.evaluate source sourceEnv [first, second]).1
          (FlatSem.evaluate flatEnv flat (compileExps trace compMap [first, second])).1 ∧
        envGenRel gen (EvaluateHOL.evaluate source sourceEnv [first, second]).1.evalState ∧
        oracForwardRel interp source.evalState (EvaluateHOL.evaluate source sourceEnv [first, second]).1.evalState
  have firstSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [first] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [first, second] = _
    simp only [sourcePair, bad]
  obtain ⟨middleGenv, headSim, headPost⟩ := firstIH genv start finish other source flat baseEnv trace baseMap gen
    value flatValue related envInv invariant generation firstSafe
  unfold ExprSim at headSim
  generalize sourceHead : EvaluateHOL.evaluate source sourceEnv [first] = sourceResult at headSim headPost
  obtain ⟨middleSource, sourceResult⟩ := sourceResult
  generalize flatHead : FlatSem.evaluate flatEnv flat [compileExp trace compMap first] = flatResult at headSim headPost
  obtain ⟨middleFlat, flatResult⟩ := flatResult
  obtain ⟨headRelated, headStates⟩ := headSim
  cases headRelated with
  | abort error =>
    refine ⟨middleGenv, ?_, ?_⟩
    · unfold ExprListSim
      rw [sourcePair, sourceHead, flatPair, flatHead]
      exact ⟨.abort error, headStates⟩
    · rw [sourcePair, sourceHead]
      trivial
  | raise headValue =>
    refine ⟨middleGenv, ?_, ?_⟩
    · unfold ExprListSim
      rw [sourcePair, sourceHead, flatPair, flatHead]
      exact ⟨.raise headValue, headStates⟩
    · rw [sourcePair, sourceHead, flatPair, flatHead]
      exact headPost
  | @value sourceValues flatValues headValues =>
    obtain ⟨sourceValue, sourceEq⟩ := EvaluateProps.evaluateSingFull source middleSource sourceEnv first sourceValues sourceHead
    subst sourceValues
    cases headValues with
    | cons headValue tailValues =>
      cases tailValues with
      | nil =>
        obtain ⟨headGrowth, middleInvariant, middleGeneration, headForward⟩ := headPost
        have middleRelated := valueRel_growth genv middleGenv headGrowth value flatValue related
        have middleEnv := globalEnvInv_growth genv middleGenv headGrowth baseMap (fun _ => False) baseEnv envInv
        have secondSafe : ∀ last, EvaluateHOL.evaluate middleSource sourceEnv [second] ≠
            (last, .err (.abort .typeError)) := by
          intro last bad
          apply safe last
          change EvaluateHOL.evaluate source sourceEnv [first, second] = _
          simp only [sourcePair, sourceHead, bad]
        obtain ⟨finalGenv, tailSim, tailPost⟩ := secondIH middleGenv start finish other middleSource middleFlat
          baseEnv trace baseMap gen value flatValue middleRelated middleEnv middleInvariant middleGeneration secondSafe
        have tailList := exprListSim_singleton finalGenv compMap trace sourceEnv flatEnv middleSource middleFlat second tailSim
        unfold ExprListSim at tailList
        generalize sourceTail : EvaluateHOL.evaluate middleSource sourceEnv [second] = sourceTailResult at tailList tailPost
        obtain ⟨finalSource, sourceTailResult⟩ := sourceTailResult
        generalize flatTail : FlatSem.evaluate flatEnv middleFlat (compileExps trace compMap [second]) = flatTailResult at tailList
        obtain ⟨finalFlat, flatTailResult⟩ := flatTailResult
        have flatTailSingleton : FlatSem.evaluate flatEnv middleFlat [compileExp trace compMap second] =
            (finalFlat, flatTailResult) := by simpa only [compileExps] using flatTail
        rw [flatTailSingleton] at tailPost
        obtain ⟨tailRelated, tailStates⟩ := tailList
        cases tailRelated with
        | abort error =>
          refine ⟨finalGenv, ?_, ?_⟩
          · unfold ExprListSim
            simp only [sourcePair, sourceHead, flatPair, flatHead, sourceTail, flatTail]
            exact ⟨.abort error, tailStates⟩
          · simp only [sourcePair, sourceHead, sourceTail]
        | raise tailValue =>
          obtain ⟨tailGrowth, finalInvariant, finalGeneration, tailForward⟩ := tailPost
          refine ⟨finalGenv, ?_, ?_⟩
          · unfold ExprListSim
            simp only [sourcePair, sourceHead, flatPair, flatHead, sourceTail, flatTail]
            exact ⟨.raise tailValue, tailStates⟩
          · simp only [sourcePair, sourceHead, flatPair, flatHead, sourceTail, flatTail]
            exact ⟨headGrowth.trans tailGrowth, finalInvariant, finalGeneration,
              oracForwardRel_trans interp _ _ _ ⟨headForward, tailForward⟩⟩
        | value tailValues =>
          obtain ⟨tailGrowth, finalInvariant, finalGeneration, tailForward⟩ := tailPost
          refine ⟨finalGenv, ?_, ?_⟩
          · unfold ExprListSim
            simp only [sourcePair, sourceHead, flatPair, flatHead, sourceTail, flatTail]
            simp only [EvaluateHOL.headValue, Flapjack.holHd]
            exact ⟨.value (.cons (valueRel_growth middleGenv finalGenv tailGrowth _ _ headValue) tailValues), tailStates⟩
          · simp only [sourcePair, sourceHead, flatPair, flatHead, sourceTail, flatTail]
            exact ⟨headGrowth.trans tailGrowth, finalInvariant, finalGeneration,
              oracForwardRel_trans interp _ _ _ ⟨headForward, tailForward⟩⟩


/-- Compose local operand hypotheses for the test primitive. -/
theorem boundLocalIH_test {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (test : Test) (typ : PrimType) (left right : AstHOL.Exp)
    (leftIH : BoundLocalIH (F := F) interp transform name left)
    (rightIH : BoundLocalIH (F := F) interp transform name right) :
    BoundLocalIH (F := F) interp transform name (.app (.test test typ) [left, right]) := by
  intro genv start finish other source flat baseEnv trace baseMap gen value flatValue related envInv invariant generation safe
  let sourceEnv := { baseEnv with v := nsBind name value baseEnv.v }
  let compMap := { baseMap with v := nsBind name (.localName .none name) baseMap.v }
  let flatEnv : FlatSem.Environment FlatSem.Value := ⟨[(name, flatValue)]⟩
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app (.test test typ) [left, right]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundLocal_pairStep interp transform genv start finish other source flat
    baseEnv trace baseMap gen name value flatValue right left rightIH leftIH related envInv invariant generation argsSafe
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



/-- Compose local operand hypotheses for the equality primitive. -/
theorem boundLocalIH_equality {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN)  (left right : AstHOL.Exp)
    (leftIH : BoundLocalIH (F := F) interp transform name left)
    (rightIH : BoundLocalIH (F := F) interp transform name right) :
    BoundLocalIH (F := F) interp transform name (.app .equality [left, right]) := by
  intro genv start finish other source flat baseEnv trace baseMap gen value flatValue related envInv invariant generation safe
  let sourceEnv := { baseEnv with v := nsBind name value baseEnv.v }
  let compMap := { baseMap with v := nsBind name (.localName .none name) baseMap.v }
  let flatEnv : FlatSem.Environment FlatSem.Value := ⟨[(name, flatValue)]⟩
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .equality [left, right]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundLocal_pairStep interp transform genv start finish other source flat
    baseEnv trace baseMap gen name value flatValue right left rightIH leftIH related envInv invariant generation argsSafe
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



/-- Compose local operand hypotheses for the integerArith primitive. -/
theorem boundLocalIH_integerArith {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (action : Arith) (left right : AstHOL.Exp)
    (leftIH : BoundLocalIH (F := F) interp transform name left)
    (rightIH : BoundLocalIH (F := F) interp transform name right) :
    BoundLocalIH (F := F) interp transform name (.app (.arith action .intT) [left, right]) := by
  intro genv start finish other source flat baseEnv trace baseMap gen value flatValue related envInv invariant generation safe
  let sourceEnv := { baseEnv with v := nsBind name value baseEnv.v }
  let compMap := { baseMap with v := nsBind name (.localName .none name) baseMap.v }
  let flatEnv : FlatSem.Environment FlatSem.Value := ⟨[(name, flatValue)]⟩
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app (.arith action .intT) [left, right]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundLocal_pairStep interp transform genv start finish other source flat
    baseEnv trace baseMap gen name value flatValue right left rightIH leftIH related envInv invariant generation argsSafe
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


/-- Local expression coverage with recursively nested binary primitives,
conditionals, and short-circuit operators. -/
inductive BoundRecursiveExpression (name : VarN) : AstHOL.Exp → Prop where
  | base (expr : AstHOL.Exp) : BoundLocalExpression name expr → BoundRecursiveExpression name expr
  | test (test : Test) (typ : PrimType) (left right : AstHOL.Exp) :
      BoundRecursiveExpression name left → BoundRecursiveExpression name right →
      BoundRecursiveExpression name (.app (.test test typ) [left, right])
  | equality (left right : AstHOL.Exp) : BoundRecursiveExpression name left → BoundRecursiveExpression name right →
      BoundRecursiveExpression name (.app .equality [left, right])
  | integerArith (action : Arith) (left right : AstHOL.Exp) :
      BoundRecursiveExpression name left → BoundRecursiveExpression name right →
      BoundRecursiveExpression name (.app (.arith action .intT) [left, right])
  | log (op : Lop) (left right : AstHOL.Exp) : BoundRecursiveExpression name left →
      BoundRecursiveExpression name right → BoundRecursiveExpression name (.log op left right)
  | if_ (cond yes no : AstHOL.Exp) : BoundRecursiveExpression name cond → BoundRecursiveExpression name yes →
      BoundRecursiveExpression name no → BoundRecursiveExpression name (.if_ cond yes no)

/-- Covered recursive local expressions satisfy the preliminary growing
induction hypothesis, whose relations remain pending HOL review. -/
theorem boundLocalIH_recursive {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (expr : AstHOL.Exp) (covered : BoundRecursiveExpression name expr) :
    BoundLocalIH (F := F) interp transform name expr := by
  induction covered with
  | base expr covered => exact boundLocalIH_covered interp transform name expr covered
  | test test typ left right _ _ leftIH rightIH =>
    exact boundLocalIH_test interp transform name test typ left right leftIH rightIH
  | equality left right _ _ leftIH rightIH =>
    exact boundLocalIH_equality interp transform name left right leftIH rightIH
  | integerArith action left right _ _ leftIH rightIH =>
    exact boundLocalIH_integerArith interp transform name action left right leftIH rightIH
  | log op left right _ _ leftIH rightIH =>
    exact boundLocalIH_log interp transform name op left right leftIH rightIH
  | if_ cond yes no _ _ _ condIH yesIH noIH =>
    exact boundLocalIH_if interp transform name cond yes no condIH yesIH noIH

/-- A named binding with a recursively covered body satisfies the factored
declaration-expression induction hypothesis. -/
theorem factoredExpressionIH_let_named_recursive {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (name : VarN) (first body : AstHOL.Exp) (covered : BoundRecursiveExpression name body)
    (firstIH : FactoredExpressionIH (F := F) interp transform first) :
    FactoredExpressionIH (F := F) interp transform (.let_ (some name) first body) := by
  apply factoredExpressionIH_let_named_of_local interp transform name first body firstIH
  exact boundLocalIH_recursive interp transform name body covered

end Flapjack.Compiler.Backend.SourceToFlat
