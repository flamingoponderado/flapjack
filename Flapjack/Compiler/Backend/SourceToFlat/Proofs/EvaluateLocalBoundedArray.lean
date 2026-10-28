import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalArray

/-! Clock-bounded array simulation over preliminary source-to-flat relations. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- Fixed array allocation evaluates its fields right-to-left, restores the
source field order, and preserves the reserved flat store entry. -/
theorem localEnvBounded_aallocFixed {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .aallocFixed args) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  change LocalExpressionStep interp transform genv start finish other source flat sourceEnv flatEnv trace compMap gen
    (.app .aallocFixed args)
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv args.reverse ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .aallocFixed args] = _
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
      simp only [compileExp, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat (compileExps trace compMap args).reverse
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      trivial
  | raise valueRel =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      simp only [compileExp, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat (compileExps trace compMap args).reverse
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.raise valueRel, states⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      simp only [compileExp, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat (compileExps trace compMap args).reverse
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact post
  | @value sourceValues flatValues valuesRel =>
    obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
    obtain ⟨sourceApp, flatApp, locationRel, stateRel, reserved⟩ :=
      aallocFixed_related nextGenv nextSource nextFlat states sourceValues.reverse flatValues.reverse
        (List.rel_reverse valuesRel)
    have finalInvariant := factoredInvariant_changeStores interp transform gen nextGenv (start, finish, other)
      nextSource nextFlat (storeAlloc (.varray sourceValues.reverse) nextSource.refs).1
      (storeAlloc (.varray flatValues.reverse) nextFlat.refs).1 nextInvariant stateRel reserved
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      simp only [compileExp, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat (compileExps trace compMap args).reverse
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      simp [getOpClass, doApp, doAppNumericCore, sourceApp, astOpToFlatOp,
        FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, flatApp, EvaluateHOL.listResult]
      exact ⟨.value (.cons locationRel .nil), stateRel⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      simp only [compileExp, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat (compileExps trace compMap args).reverse
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      simpa [getOpClass, doApp, doAppNumericCore, sourceApp, astOpToFlatOp,
        FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, flatApp, EvaluateHOL.listResult] using
        And.intro growth (And.intro finalInvariant (And.intro nextGeneration forward))

/-- Compose dynamic array allocation operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_aalloc {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .aalloc [left, right]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .aalloc [left, right]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform limit [right, left]
    (by intro expr member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl <;> assumption)
    genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
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
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.raise valueRel, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact post
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
    obtain ⟨sourceValue, sourceSize, rfl⟩ := two
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | cons sizeRel tail =>
        cases tail with
        | nil =>
          rename_i flatValue flatSize
          obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
          have successful : doApp (nextSource.refs, nextSource.ffi) .aalloc [sourceSize, sourceValue] ≠ none := by
            intro failed
            apply safe nextSource
            change EvaluateHOL.evaluate source sourceEnv [.app .aalloc [left, right]] = _
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp [getOpClass, failed, EvaluateHOL.typeError]
          obtain ⟨size, rfl⟩ := aalloc_size_operand nextSource sourceSize sourceValue successful
          have flatSizeEq := (valueRel_literal_iff nextGenv (.intLit size) flatSize).mp sizeRel
          subst flatSize
          by_cases negative : size < 0
          · refine ⟨nextGenv, ?_, ?_⟩
            · unfold ExprSim
              rw [EvaluateHOL.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
              rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
              simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
              rw [FlatSem.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
              rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap right, compileExp trace compMap left]
                (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
              simp [getOpClass, doApp, doAppNumericCore, doAppBasic, boundsFailure, negative, astOpToFlatOp,
                FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                FlatSem.boundsFailure, EvaluateHOL.listResult]
              exact ⟨.raise (exceptionValues_related nextGenv nextInvariant.1).2.2.2, states⟩
            ·
              rw [EvaluateHOL.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
              rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
              simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
              rw [FlatSem.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
              rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap right, compileExp trace compMap left]
                (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
              simpa [getOpClass, doApp, doAppNumericCore, doAppBasic, boundsFailure, negative, astOpToFlatOp,
                FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                FlatSem.boundsFailure, EvaluateHOL.listResult] using
                And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))
          · have nonnegative : 0 ≤ size := Int.le_of_not_gt negative
            obtain ⟨sourceApp, flatApp, locationRel, stateRel, reserved⟩ :=
              aalloc_related nextGenv nextSource nextFlat states size nonnegative sourceValue flatValue valueRel
            have finalInvariant := factoredInvariant_changeStores interp transform gen nextGenv (start, finish, other)
              nextSource nextFlat (storeAlloc (.varray (List.replicate size.toNat sourceValue)) nextSource.refs).1
              (storeAlloc (.varray (List.replicate size.toNat flatValue)) nextFlat.refs).1 nextInvariant stateRel reserved
            refine ⟨nextGenv, ?_, ?_⟩
            · unfold ExprSim
              rw [EvaluateHOL.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
              rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
              simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
              rw [FlatSem.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
              rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap right, compileExp trace compMap left]
                (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
              simp [getOpClass, doApp, doAppNumericCore, sourceApp, astOpToFlatOp,
                FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, flatApp, EvaluateHOL.listResult]
              exact ⟨.value (.cons locationRel .nil), stateRel⟩
            ·
              rw [EvaluateHOL.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
              rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
              simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
              rw [FlatSem.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
              rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap right, compileExp trace compMap left]
                (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
              simpa [getOpClass, doApp, doAppNumericCore, sourceApp, astOpToFlatOp,
                FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, flatApp, EvaluateHOL.listResult] using
                And.intro growth (And.intro finalInvariant (And.intro nextGeneration forward))

/-- Compose dynamic byte-array allocation operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_aw8alloc {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .aw8alloc [left, right]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .aw8alloc [left, right]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform limit [right, left]
    (by intro expr member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl <;> assumption)
    genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
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
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.raise valueRel, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact post
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
    obtain ⟨sourceValue, sourceSize, rfl⟩ := two
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | cons sizeRel tail =>
        cases tail with
        | nil =>
          rename_i flatValue flatSize
          obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
          have successful : doApp (nextSource.refs, nextSource.ffi) .aw8alloc [sourceSize, sourceValue] ≠ none := by
            intro failed
            apply safe nextSource
            change EvaluateHOL.evaluate source sourceEnv [.app .aw8alloc [left, right]] = _
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp [getOpClass, failed, EvaluateHOL.typeError]
          obtain ⟨size, byte, rfl, rfl⟩ := aw8alloc_operands nextSource sourceSize sourceValue successful
          have flatValueEq := (valueRel_literal_iff nextGenv (.word8 byte) flatValue).mp valueRel
          subst flatValue
          have flatSizeEq := (valueRel_literal_iff nextGenv (.intLit size) flatSize).mp sizeRel
          subst flatSize
          by_cases negative : size < 0
          · refine ⟨nextGenv, ?_, ?_⟩
            · unfold ExprSim
              rw [EvaluateHOL.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
              rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
              simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
              rw [FlatSem.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
              rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap right, compileExp trace compMap left]
                (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
              simp [getOpClass, doApp, doAppNumericCore, doAppBasic, boundsFailure, negative, astOpToFlatOp,
                FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                FlatSem.boundsFailure, EvaluateHOL.listResult]
              exact ⟨.raise (exceptionValues_related nextGenv nextInvariant.1).2.2.2, states⟩
            ·
              rw [EvaluateHOL.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
              rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
              simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
              rw [FlatSem.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
              rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap right, compileExp trace compMap left]
                (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
              simpa [getOpClass, doApp, doAppNumericCore, doAppBasic, boundsFailure, negative, astOpToFlatOp,
                FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                FlatSem.boundsFailure, EvaluateHOL.listResult] using
                And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))
          · have nonnegative : 0 ≤ size := Int.le_of_not_gt negative
            obtain ⟨sourceApp, flatApp, locationRel, stateRel, reserved⟩ :=
              aw8alloc_related nextGenv nextSource nextFlat states size nonnegative byte
            have finalInvariant := factoredInvariant_changeStores interp transform gen nextGenv (start, finish, other)
              nextSource nextFlat (storeAlloc (.w8array (List.replicate size.toNat byte)) nextSource.refs).1
              (storeAlloc (.w8array (List.replicate size.toNat byte)) nextFlat.refs).1 nextInvariant stateRel reserved
            refine ⟨nextGenv, ?_, ?_⟩
            · unfold ExprSim
              rw [EvaluateHOL.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
              rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
              simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
              rw [FlatSem.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
              rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap right, compileExp trace compMap left]
                (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
              simp [getOpClass, doApp, doAppNumericCore, sourceApp, astOpToFlatOp,
                FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, flatApp, EvaluateHOL.listResult]
              exact ⟨.value (.cons locationRel .nil), stateRel⟩
            ·
              rw [EvaluateHOL.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
              rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
              simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
              rw [FlatSem.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
              rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap right, compileExp trace compMap left]
                (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
              simpa [getOpClass, doApp, doAppNumericCore, sourceApp, astOpToFlatOp,
                FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, flatApp, EvaluateHOL.listResult] using
                And.intro growth (And.intro finalInvariant (And.intro nextGeneration forward))

/-- alength expressions compose a growing operand simulation in a local environment. -/
theorem localEnvBounded_alength {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .alength [body]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have bodySafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .alength [body]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, bad]
  obtain ⟨nextGenv, bodySim, post⟩ := bodyIH genv start finish other source flat baseEnv sourceLocal flatEnv traces
    trace baseMap gen clockBound localRel envInv tracesLen invariant generation bodySafe
  have bodySimCopy := bodySim
  unfold ExprSim at bodySim
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [body] = sourceResult at bodySim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap body] = flatResult at bodySim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := bodySim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      trivial
  | raise valueRel =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.raise valueRel, states⟩
    ·
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact post
  | @value sourceValues flatValues valuesRel =>
    obtain ⟨operand, rfl⟩ := EvaluateProps.evaluateSingFull source nextSource sourceEnv body sourceValues sourceRun
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | nil =>
        rename_i flatOperand
        obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
        have successful : doApp (nextSource.refs, nextSource.ffi) .alength [operand] ≠ none := by
          intro failed
          apply safe nextSource
          change EvaluateHOL.evaluate source sourceEnv [.app .alength [body]] = _
          rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp [getOpClass, failed, EvaluateHOL.typeError]
        obtain ⟨flag, address, contents, rfl, lookup⟩ := alength_operand nextSource operand successful
        have flatLocation := (valueRel_location_iff nextGenv flag address flatOperand).mp valueRel
        subst flatOperand
        obtain ⟨sourceApp, flatApp, resultRel⟩ := alength_related nextGenv nextSource nextFlat states flag address contents lookup
        refine ⟨nextGenv, ?_, ?_⟩
        · unfold ExprSim
          rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
          rw [FlatSem.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
            (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
          simp [getOpClass, doApp, doAppNumericCore, sourceApp, astOpToFlatOp,
            FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, flatApp, EvaluateHOL.listResult]
          exact ⟨.value (.cons resultRel .nil), states⟩
        ·
          rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
          rw [FlatSem.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
            (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
          simpa [getOpClass, doApp, doAppNumericCore, sourceApp, astOpToFlatOp,
            FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, flatApp, EvaluateHOL.listResult] using
            And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))

/-- aw8length expressions compose a growing operand simulation in a local environment. -/
theorem localEnvBounded_aw8length {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .aw8length [body]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have bodySafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .aw8length [body]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, bad]
  obtain ⟨nextGenv, bodySim, post⟩ := bodyIH genv start finish other source flat baseEnv sourceLocal flatEnv traces
    trace baseMap gen clockBound localRel envInv tracesLen invariant generation bodySafe
  have bodySimCopy := bodySim
  unfold ExprSim at bodySim
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [body] = sourceResult at bodySim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap body] = flatResult at bodySim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := bodySim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      trivial
  | raise valueRel =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.raise valueRel, states⟩
    ·
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact post
  | @value sourceValues flatValues valuesRel =>
    obtain ⟨operand, rfl⟩ := EvaluateProps.evaluateSingFull source nextSource sourceEnv body sourceValues sourceRun
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | nil =>
        rename_i flatOperand
        obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
        have successful : doApp (nextSource.refs, nextSource.ffi) .aw8length [operand] ≠ none := by
          intro failed
          apply safe nextSource
          change EvaluateHOL.evaluate source sourceEnv [.app .aw8length [body]] = _
          rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp [getOpClass, failed, EvaluateHOL.typeError]
        obtain ⟨flag, address, contents, rfl, lookup⟩ := aw8length_operand nextSource operand successful
        have flatLocation := (valueRel_location_iff nextGenv flag address flatOperand).mp valueRel
        subst flatOperand
        obtain ⟨sourceApp, flatApp, resultRel⟩ := aw8length_related nextGenv nextSource nextFlat states flag address contents lookup
        refine ⟨nextGenv, ?_, ?_⟩
        · unfold ExprSim
          rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
          rw [FlatSem.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
            (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
          simp [getOpClass, doApp, doAppNumericCore, sourceApp, astOpToFlatOp,
            FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, flatApp, EvaluateHOL.listResult]
          exact ⟨.value (.cons resultRel .nil), states⟩
        ·
          rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
          rw [FlatSem.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
            (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
          simpa [getOpClass, doApp, doAppNumericCore, sourceApp, astOpToFlatOp,
            FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, flatApp, EvaluateHOL.listResult] using
            And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))

/-- Compose aw8sub operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_aw8sub {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .aw8sub [left, right]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .aw8sub [left, right]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform limit [right, left]
    (by intro expr member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl <;> assumption)
    genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
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
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.raise valueRel, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact post
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
    obtain ⟨sourceValue, sourceSize, rfl⟩ := two
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | cons sizeRel tail =>
        cases tail with
        | nil =>
          rename_i flatValue flatSize
          obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
          have successful : doApp (nextSource.refs, nextSource.ffi) .aw8sub [sourceSize, sourceValue] ≠ none := by
            intro failed
            apply safe nextSource
            change EvaluateHOL.evaluate source sourceEnv [.app .aw8sub [left, right]] = _
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp [getOpClass, failed, EvaluateHOL.typeError]
          obtain ⟨flag, address, index, bytes, rfl, rfl, lookup⟩ :=
            aw8sub_operands nextSource sourceSize sourceValue false successful
          have flatLocation := (valueRel_location_iff nextGenv flag address flatSize).mp sizeRel
          have flatIndex := (valueRel_literal_iff nextGenv (.intLit index) flatValue).mp valueRel
          subst flatSize
          subst flatValue
          have primitive := aw8sub_complete_related nextGenv nextSource nextFlat states nextInvariant.1
            flag address bytes lookup index false
          simp only [Bool.false_eq_true, if_false] at primitive
          cases sourceApp : doApp (nextSource.refs, nextSource.ffi) .aw8sub
              [.loc flag address, .litv (.intLit index)] with
          | none => exact (successful sourceApp).elim
          | some sourceOut =>
            cases sourceOut with
            | mk store sourceResult =>
              cases store with
              | mk refs ffi =>
                cases flatApp : FlatSem.doAppMemory nextFlat .aw8sub
                    [.loc flag (address + 1), .litv (.intLit index)] with
                | none => simp [sourceApp, flatApp] at primitive
                | some flatOut =>
                  cases flatOut with
                  | none => simp [sourceApp, flatApp] at primitive
                  | some flatOut =>
                    cases flatOut with
                    | mk flatAfter flatResult =>
                      simp only [sourceApp, flatApp] at primitive
                      obtain ⟨rfl, rfl, rfl, resultRel⟩ := primitive
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
                        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                          getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp,
                          FlatSem.doAppNumeric, flatApp]
                        cases resultRel with
                        | value valueRel => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.value (.cons valueRel .nil)) states
                        | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.raise valueRel) states
                        | abort error => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.abort error) states
                      · rw [EvaluateHOL.evaluate]
                        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                        rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
                        simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                        rw [FlatSem.evaluate]
                        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                        rw [(FlatSem.fixClock_evaluations flatEnv flat
                          [compileExp trace compMap right, compileExp trace compMap left]
                          (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
                        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                          getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp,
                          FlatSem.doAppNumeric, flatApp]
                        cases resultRel with
                        | value valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))
                        | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))
                        | abort error => simp [EvaluateHOL.listResult]

/-- Compose aw8subUnsafe operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_aw8subUnsafe {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .aw8subUnsafe [left, right]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .aw8subUnsafe [left, right]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform limit [right, left]
    (by intro expr member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl <;> assumption)
    genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
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
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.raise valueRel, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact post
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
    obtain ⟨sourceValue, sourceSize, rfl⟩ := two
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | cons sizeRel tail =>
        cases tail with
        | nil =>
          rename_i flatValue flatSize
          obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
          have successful : doApp (nextSource.refs, nextSource.ffi) .aw8subUnsafe [sourceSize, sourceValue] ≠ none := by
            intro failed
            apply safe nextSource
            change EvaluateHOL.evaluate source sourceEnv [.app .aw8subUnsafe [left, right]] = _
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp [getOpClass, failed, EvaluateHOL.typeError]
          obtain ⟨flag, address, index, bytes, rfl, rfl, lookup⟩ :=
            aw8sub_operands nextSource sourceSize sourceValue true successful
          have flatLocation := (valueRel_location_iff nextGenv flag address flatSize).mp sizeRel
          have flatIndex := (valueRel_literal_iff nextGenv (.intLit index) flatValue).mp valueRel
          subst flatSize
          subst flatValue
          have primitive := aw8sub_complete_related nextGenv nextSource nextFlat states nextInvariant.1
            flag address bytes lookup index true
          simp only [if_true] at primitive
          cases sourceApp : doApp (nextSource.refs, nextSource.ffi) .aw8subUnsafe
              [.loc flag address, .litv (.intLit index)] with
          | none => exact (successful sourceApp).elim
          | some sourceOut =>
            cases sourceOut with
            | mk store sourceResult =>
              cases store with
              | mk refs ffi =>
                cases flatApp : FlatSem.doAppMemory nextFlat .aw8subUnsafe
                    [.loc flag (address + 1), .litv (.intLit index)] with
                | none => simp [sourceApp, flatApp] at primitive
                | some flatOut =>
                  cases flatOut with
                  | none => simp [sourceApp, flatApp] at primitive
                  | some flatOut =>
                    cases flatOut with
                    | mk flatAfter flatResult =>
                      simp only [sourceApp, flatApp] at primitive
                      obtain ⟨rfl, rfl, rfl, resultRel⟩ := primitive
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
                        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                          getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp,
                          FlatSem.doAppNumeric, flatApp]
                        cases resultRel with
                        | value valueRel => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.value (.cons valueRel .nil)) states
                        | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.raise valueRel) states
                        | abort error => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.abort error) states
                      · rw [EvaluateHOL.evaluate]
                        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                        rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
                        simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                        rw [FlatSem.evaluate]
                        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                        rw [(FlatSem.fixClock_evaluations flatEnv flat
                          [compileExp trace compMap right, compileExp trace compMap left]
                          (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
                        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                          getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp,
                          FlatSem.doAppNumeric, flatApp]
                        cases resultRel with
                        | value valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))
                        | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))
                        | abort error => simp [EvaluateHOL.listResult]

/-- Compose asub operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_asub {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .asub [left, right]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .asub [left, right]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform limit [right, left]
    (by intro expr member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl <;> assumption)
    genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
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
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.raise valueRel, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact post
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
    obtain ⟨sourceValue, sourceSize, rfl⟩ := two
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | cons sizeRel tail =>
        cases tail with
        | nil =>
          rename_i flatValue flatSize
          obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
          have successful : doApp (nextSource.refs, nextSource.ffi) .asub [sourceSize, sourceValue] ≠ none := by
            intro failed
            apply safe nextSource
            change EvaluateHOL.evaluate source sourceEnv [.app .asub [left, right]] = _
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp [getOpClass, failed, EvaluateHOL.typeError]
          obtain ⟨flag, address, index, bytes, rfl, rfl, lookup⟩ :=
            asub_operands nextSource sourceSize sourceValue false successful
          have flatLocation := (valueRel_location_iff nextGenv flag address flatSize).mp sizeRel
          have flatIndex := (valueRel_literal_iff nextGenv (.intLit index) flatValue).mp valueRel
          subst flatSize
          subst flatValue
          have primitive := asub_complete_related nextGenv nextSource nextFlat states nextInvariant.1
            flag address bytes lookup index false
          simp only [Bool.false_eq_true, if_false] at primitive
          cases sourceApp : doApp (nextSource.refs, nextSource.ffi) .asub
              [.loc flag address, .litv (.intLit index)] with
          | none => exact (successful sourceApp).elim
          | some sourceOut =>
            cases sourceOut with
            | mk store sourceResult =>
              cases store with
              | mk refs ffi =>
                cases flatApp : FlatSem.doAppMemory nextFlat .asub
                    [.loc flag (address + 1), .litv (.intLit index)] with
                | none => simp [sourceApp, flatApp] at primitive
                | some flatOut =>
                  cases flatOut with
                  | none => simp [sourceApp, flatApp] at primitive
                  | some flatOut =>
                    cases flatOut with
                    | mk flatAfter flatResult =>
                      simp only [sourceApp, flatApp] at primitive
                      obtain ⟨rfl, rfl, rfl, resultRel⟩ := primitive
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
                        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                          getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp,
                          FlatSem.doAppNumeric, flatApp]
                        cases resultRel with
                        | value valueRel => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.value (.cons valueRel .nil)) states
                        | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.raise valueRel) states
                        | abort error => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.abort error) states
                      · rw [EvaluateHOL.evaluate]
                        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                        rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
                        simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                        rw [FlatSem.evaluate]
                        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                        rw [(FlatSem.fixClock_evaluations flatEnv flat
                          [compileExp trace compMap right, compileExp trace compMap left]
                          (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
                        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                          getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp,
                          FlatSem.doAppNumeric, flatApp]
                        cases resultRel with
                        | value valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))
                        | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))
                        | abort error => simp [EvaluateHOL.listResult]

/-- Compose asubUnsafe operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_asubUnsafe {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .asubUnsafe [left, right]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .asubUnsafe [left, right]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform limit [right, left]
    (by intro expr member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl <;> assumption)
    genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
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
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.raise valueRel, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact post
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
    obtain ⟨sourceValue, sourceSize, rfl⟩ := two
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | cons sizeRel tail =>
        cases tail with
        | nil =>
          rename_i flatValue flatSize
          obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
          have successful : doApp (nextSource.refs, nextSource.ffi) .asubUnsafe [sourceSize, sourceValue] ≠ none := by
            intro failed
            apply safe nextSource
            change EvaluateHOL.evaluate source sourceEnv [.app .asubUnsafe [left, right]] = _
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp [getOpClass, failed, EvaluateHOL.typeError]
          obtain ⟨flag, address, index, bytes, rfl, rfl, lookup⟩ :=
            asub_operands nextSource sourceSize sourceValue true successful
          have flatLocation := (valueRel_location_iff nextGenv flag address flatSize).mp sizeRel
          have flatIndex := (valueRel_literal_iff nextGenv (.intLit index) flatValue).mp valueRel
          subst flatSize
          subst flatValue
          have primitive := asub_complete_related nextGenv nextSource nextFlat states nextInvariant.1
            flag address bytes lookup index true
          simp only [if_true] at primitive
          cases sourceApp : doApp (nextSource.refs, nextSource.ffi) .asubUnsafe
              [.loc flag address, .litv (.intLit index)] with
          | none => exact (successful sourceApp).elim
          | some sourceOut =>
            cases sourceOut with
            | mk store sourceResult =>
              cases store with
              | mk refs ffi =>
                cases flatApp : FlatSem.doAppMemory nextFlat .asubUnsafe
                    [.loc flag (address + 1), .litv (.intLit index)] with
                | none => simp [sourceApp, flatApp] at primitive
                | some flatOut =>
                  cases flatOut with
                  | none => simp [sourceApp, flatApp] at primitive
                  | some flatOut =>
                    cases flatOut with
                    | mk flatAfter flatResult =>
                      simp only [sourceApp, flatApp] at primitive
                      obtain ⟨rfl, rfl, rfl, resultRel⟩ := primitive
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
                        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                          getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp,
                          FlatSem.doAppNumeric, flatApp]
                        cases resultRel with
                        | value valueRel => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.value (.cons valueRel .nil)) states
                        | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.raise valueRel) states
                        | abort error => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.abort error) states
                      · rw [EvaluateHOL.evaluate]
                        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                        rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
                        simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                        rw [FlatSem.evaluate]
                        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                        rw [(FlatSem.fixClock_evaluations flatEnv flat
                          [compileExp trace compMap right, compileExp trace compMap left]
                          (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
                        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                          getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp,
                          FlatSem.doAppNumeric, flatApp]
                        cases resultRel with
                        | value valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))
                        | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))
                        | abort error => simp [EvaluateHOL.listResult]

/-- Compose aupdate operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_aupdate {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right third : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right)
    (thirdIH : LocalEnvBoundedIH (F := F) interp transform limit third) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .aupdate [left, right, third]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [third, right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .aupdate [left, right, third]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform limit [third, right, left]
    (by intro expr member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl <;> assumption)
    genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
  unfold ExprListSim at argsSim
  simp only [compileExps] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [third, right, left] = sourceResult at argsSim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left] = flatResult at argsSim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := argsSim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
      trivial
  | raise valueRel =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.raise valueRel, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact post
  | @value sourceValues flatValues valuesRel =>
    have length := EvaluateProps.evaluateLengthFull source nextSource sourceEnv [third, right, left] sourceValues sourceRun
    have three : ∃ v i p, sourceValues = [v, i, p] := by
      cases sourceValues with
      | nil => simp at length
      | cons v tail =>
        cases tail with
        | nil => simp at length
        | cons i tail =>
          cases tail with
          | nil => simp at length
          | cons p rest =>
            cases rest with
            | nil => exact ⟨v, i, p, rfl⟩
            | cons q rest => simp at length
    obtain ⟨sourceValue, sourceIndex, sourcePointer, rfl⟩ := three
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | cons indexRel tail =>
        cases tail with
        | cons pointerRel tail =>
          cases tail with
          | nil =>
            rename_i flatValue flatIndex flatPointer
            obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
            have successful : doApp (nextSource.refs, nextSource.ffi) .aupdate [sourcePointer, sourceIndex, sourceValue] ≠ none := by
              intro failed
              apply safe nextSource
              change EvaluateHOL.evaluate source sourceEnv [.app .aupdate [left, right, third]] = _
              rw [EvaluateHOL.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
              rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
              simp [getOpClass, failed, EvaluateHOL.typeError]
            obtain ⟨flag, address, index, values, rfl, rfl, lookup⟩ :=
              aupdate_operands nextSource sourcePointer sourceIndex sourceValue false successful
            have flatLocation := (valueRel_location_iff nextGenv flag address flatPointer).mp pointerRel
            have flatIndexEq := (valueRel_literal_iff nextGenv (.intLit index) flatIndex).mp indexRel
            subst flatPointer
            subst flatIndex
            have primitive := aupdate_complete_related nextGenv nextSource nextFlat states nextInvariant.1
              flag address values lookup index sourceValue flatValue valueRel false
            simp only [Bool.false_eq_true, if_false] at primitive
            cases sourceApp : doApp (nextSource.refs, nextSource.ffi) .aupdate
                [.loc flag address, .litv (.intLit index), sourceValue] with
            | none => exact (successful sourceApp).elim
            | some sourceOut =>
              cases sourceOut with
              | mk store sourceResult =>
                cases store with
                | mk refs ffi =>
                  cases flatApp : FlatSem.doAppMemory nextFlat .aupdate
                      [.loc flag (address + 1), .litv (.intLit index), flatValue] with
                  | none => simp [sourceApp, flatApp] at primitive
                  | some flatOut =>
                    cases flatOut with
                    | none => simp [sourceApp, flatApp] at primitive
                    | some flatOut =>
                      cases flatOut with
                      | mk flatAfter flatResult =>
                        simp only [sourceApp, flatApp] at primitive
                        obtain ⟨rfl, flatEq, stateRel, reserved, resultRel⟩ := primitive
                        have finalInvariant := factoredInvariant_changeStores interp transform gen nextGenv (start, finish, other)
                          nextSource nextFlat refs flatAfter.refs nextInvariant (by rw [flatEq] at stateRel; exact stateRel) reserved
                        have finalInvariant' : factoredInvariant interp transform gen nextGenv (start, finish, other)
                            { nextSource with refs := refs } flatAfter := by
                          rw [flatEq]
                          exact finalInvariant
                        refine ⟨nextGenv, ?_, ?_⟩
                        · unfold ExprSim
                          rw [EvaluateHOL.evaluate]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
                          simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                          rw [FlatSem.evaluate]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                          rw [(FlatSem.fixClock_evaluations flatEnv flat
                            [compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
                            (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                            getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp,
                            FlatSem.doAppNumeric, flatApp]
                          cases resultRel with
                          | value valueRel => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.value (.cons valueRel .nil)) stateRel
                          | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.raise valueRel) stateRel
                          | abort error => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.abort error) stateRel
                        · rw [EvaluateHOL.evaluate]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
                          simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                          rw [FlatSem.evaluate]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                          rw [(FlatSem.fixClock_evaluations flatEnv flat
                            [compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
                            (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                            getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp,
                            FlatSem.doAppNumeric, flatApp]
                          cases resultRel with
                          | value valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro finalInvariant' (And.intro nextGeneration forward))
                          | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro finalInvariant' (And.intro nextGeneration forward))
                          | abort error => simp [EvaluateHOL.listResult]

/-- Compose aupdateUnsafe operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_aupdateUnsafe {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right third : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right)
    (thirdIH : LocalEnvBoundedIH (F := F) interp transform limit third) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .aupdateUnsafe [left, right, third]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [third, right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .aupdateUnsafe [left, right, third]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform limit [third, right, left]
    (by intro expr member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl <;> assumption)
    genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
  unfold ExprListSim at argsSim
  simp only [compileExps] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [third, right, left] = sourceResult at argsSim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left] = flatResult at argsSim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := argsSim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
      trivial
  | raise valueRel =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.raise valueRel, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact post
  | @value sourceValues flatValues valuesRel =>
    have length := EvaluateProps.evaluateLengthFull source nextSource sourceEnv [third, right, left] sourceValues sourceRun
    have three : ∃ v i p, sourceValues = [v, i, p] := by
      cases sourceValues with
      | nil => simp at length
      | cons v tail =>
        cases tail with
        | nil => simp at length
        | cons i tail =>
          cases tail with
          | nil => simp at length
          | cons p rest =>
            cases rest with
            | nil => exact ⟨v, i, p, rfl⟩
            | cons q rest => simp at length
    obtain ⟨sourceValue, sourceIndex, sourcePointer, rfl⟩ := three
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | cons indexRel tail =>
        cases tail with
        | cons pointerRel tail =>
          cases tail with
          | nil =>
            rename_i flatValue flatIndex flatPointer
            obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
            have successful : doApp (nextSource.refs, nextSource.ffi) .aupdateUnsafe [sourcePointer, sourceIndex, sourceValue] ≠ none := by
              intro failed
              apply safe nextSource
              change EvaluateHOL.evaluate source sourceEnv [.app .aupdateUnsafe [left, right, third]] = _
              rw [EvaluateHOL.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
              rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
              simp [getOpClass, failed, EvaluateHOL.typeError]
            obtain ⟨flag, address, index, values, rfl, rfl, lookup⟩ :=
              aupdate_operands nextSource sourcePointer sourceIndex sourceValue true successful
            have flatLocation := (valueRel_location_iff nextGenv flag address flatPointer).mp pointerRel
            have flatIndexEq := (valueRel_literal_iff nextGenv (.intLit index) flatIndex).mp indexRel
            subst flatPointer
            subst flatIndex
            have primitive := aupdate_complete_related nextGenv nextSource nextFlat states nextInvariant.1
              flag address values lookup index sourceValue flatValue valueRel true
            simp only [if_true] at primitive
            cases sourceApp : doApp (nextSource.refs, nextSource.ffi) .aupdateUnsafe
                [.loc flag address, .litv (.intLit index), sourceValue] with
            | none => exact (successful sourceApp).elim
            | some sourceOut =>
              cases sourceOut with
              | mk store sourceResult =>
                cases store with
                | mk refs ffi =>
                  cases flatApp : FlatSem.doAppMemory nextFlat .aupdateUnsafe
                      [.loc flag (address + 1), .litv (.intLit index), flatValue] with
                  | none => simp [sourceApp, flatApp] at primitive
                  | some flatOut =>
                    cases flatOut with
                    | none => simp [sourceApp, flatApp] at primitive
                    | some flatOut =>
                      cases flatOut with
                      | mk flatAfter flatResult =>
                        simp only [sourceApp, flatApp] at primitive
                        obtain ⟨rfl, flatEq, stateRel, reserved, resultRel⟩ := primitive
                        have finalInvariant := factoredInvariant_changeStores interp transform gen nextGenv (start, finish, other)
                          nextSource nextFlat refs flatAfter.refs nextInvariant (by rw [flatEq] at stateRel; exact stateRel) reserved
                        have finalInvariant' : factoredInvariant interp transform gen nextGenv (start, finish, other)
                            { nextSource with refs := refs } flatAfter := by
                          rw [flatEq]
                          exact finalInvariant
                        refine ⟨nextGenv, ?_, ?_⟩
                        · unfold ExprSim
                          rw [EvaluateHOL.evaluate]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
                          simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                          rw [FlatSem.evaluate]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                          rw [(FlatSem.fixClock_evaluations flatEnv flat
                            [compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
                            (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                            getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp,
                            FlatSem.doAppNumeric, flatApp]
                          cases resultRel with
                          | value valueRel => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.value (.cons valueRel .nil)) stateRel
                          | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.raise valueRel) stateRel
                          | abort error => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.abort error) stateRel
                        · rw [EvaluateHOL.evaluate]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
                          simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                          rw [FlatSem.evaluate]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                          rw [(FlatSem.fixClock_evaluations flatEnv flat
                            [compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
                            (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                            getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp,
                            FlatSem.doAppNumeric, flatApp]
                          cases resultRel with
                          | value valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro finalInvariant' (And.intro nextGeneration forward))
                          | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro finalInvariant' (And.intro nextGeneration forward))
                          | abort error => simp [EvaluateHOL.listResult]

/-- Compose aw8update operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_aw8update {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right third : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right)
    (thirdIH : LocalEnvBoundedIH (F := F) interp transform limit third) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .aw8update [left, right, third]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [third, right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .aw8update [left, right, third]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform limit [third, right, left]
    (by intro expr member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl <;> assumption)
    genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
  unfold ExprListSim at argsSim
  simp only [compileExps] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [third, right, left] = sourceResult at argsSim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left] = flatResult at argsSim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := argsSim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
      trivial
  | raise valueRel =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.raise valueRel, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact post
  | @value sourceValues flatValues valuesRel =>
    have length := EvaluateProps.evaluateLengthFull source nextSource sourceEnv [third, right, left] sourceValues sourceRun
    have three : ∃ v i p, sourceValues = [v, i, p] := by
      cases sourceValues with
      | nil => simp at length
      | cons v tail =>
        cases tail with
        | nil => simp at length
        | cons i tail =>
          cases tail with
          | nil => simp at length
          | cons p rest =>
            cases rest with
            | nil => exact ⟨v, i, p, rfl⟩
            | cons q rest => simp at length
    obtain ⟨sourceValue, sourceIndex, sourcePointer, rfl⟩ := three
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | cons indexRel tail =>
        cases tail with
        | cons pointerRel tail =>
          cases tail with
          | nil =>
            rename_i flatValue flatIndex flatPointer
            obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
            have successful : doApp (nextSource.refs, nextSource.ffi) .aw8update [sourcePointer, sourceIndex, sourceValue] ≠ none := by
              intro failed
              apply safe nextSource
              change EvaluateHOL.evaluate source sourceEnv [.app .aw8update [left, right, third]] = _
              rw [EvaluateHOL.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
              rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
              simp [getOpClass, failed, EvaluateHOL.typeError]
            obtain ⟨flag, address, index, byte, values, rfl, rfl, rfl, lookup⟩ :=
              aw8update_operands nextSource sourcePointer sourceIndex sourceValue false successful
            have flatLocation := (valueRel_location_iff nextGenv flag address flatPointer).mp pointerRel
            have flatIndexEq := (valueRel_literal_iff nextGenv (.intLit index) flatIndex).mp indexRel
            have flatValueEq := (valueRel_literal_iff nextGenv (.word8 byte) flatValue).mp valueRel
            subst flatPointer
            subst flatIndex
            subst flatValue
            have primitive := aw8update_complete_related nextGenv nextSource nextFlat states nextInvariant.1
              flag address values lookup index byte false
            simp only [Bool.false_eq_true, if_false] at primitive
            cases sourceApp : doApp (nextSource.refs, nextSource.ffi) .aw8update
                [.loc flag address, .litv (.intLit index), .litv (.word8 byte)] with
            | none => exact (successful sourceApp).elim
            | some sourceOut =>
              cases sourceOut with
              | mk store sourceResult =>
                cases store with
                | mk refs ffi =>
                  cases flatApp : FlatSem.doAppMemory nextFlat .aw8update
                      [.loc flag (address + 1), .litv (.intLit index), .litv (.word8 byte)] with
                  | none => simp [sourceApp, flatApp] at primitive
                  | some flatOut =>
                    cases flatOut with
                    | none => simp [sourceApp, flatApp] at primitive
                    | some flatOut =>
                      cases flatOut with
                      | mk flatAfter flatResult =>
                        simp only [sourceApp, flatApp] at primitive
                        obtain ⟨rfl, flatEq, stateRel, reserved, resultRel⟩ := primitive
                        have finalInvariant := factoredInvariant_changeStores interp transform gen nextGenv (start, finish, other)
                          nextSource nextFlat refs flatAfter.refs nextInvariant (by rw [flatEq] at stateRel; exact stateRel) reserved
                        have finalInvariant' : factoredInvariant interp transform gen nextGenv (start, finish, other)
                            { nextSource with refs := refs } flatAfter := by
                          rw [flatEq]
                          exact finalInvariant
                        refine ⟨nextGenv, ?_, ?_⟩
                        · unfold ExprSim
                          rw [EvaluateHOL.evaluate]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
                          simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                          rw [FlatSem.evaluate]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                          rw [(FlatSem.fixClock_evaluations flatEnv flat
                            [compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
                            (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                            getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp,
                            FlatSem.doAppNumeric, flatApp]
                          cases resultRel with
                          | value valueRel => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.value (.cons valueRel .nil)) stateRel
                          | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.raise valueRel) stateRel
                          | abort error => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.abort error) stateRel
                        · rw [EvaluateHOL.evaluate]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
                          simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                          rw [FlatSem.evaluate]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                          rw [(FlatSem.fixClock_evaluations flatEnv flat
                            [compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
                            (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                            getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp,
                            FlatSem.doAppNumeric, flatApp]
                          cases resultRel with
                          | value valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro finalInvariant' (And.intro nextGeneration forward))
                          | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro finalInvariant' (And.intro nextGeneration forward))
                          | abort error => simp [EvaluateHOL.listResult]

/-- Compose aw8updateUnsafe operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_aw8updateUnsafe {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right third : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right)
    (thirdIH : LocalEnvBoundedIH (F := F) interp transform limit third) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .aw8updateUnsafe [left, right, third]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [third, right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .aw8updateUnsafe [left, right, third]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform limit [third, right, left]
    (by intro expr member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl <;> assumption)
    genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
  unfold ExprListSim at argsSim
  simp only [compileExps] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [third, right, left] = sourceResult at argsSim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left] = flatResult at argsSim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := argsSim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
      trivial
  | raise valueRel =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.raise valueRel, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact post
  | @value sourceValues flatValues valuesRel =>
    have length := EvaluateProps.evaluateLengthFull source nextSource sourceEnv [third, right, left] sourceValues sourceRun
    have three : ∃ v i p, sourceValues = [v, i, p] := by
      cases sourceValues with
      | nil => simp at length
      | cons v tail =>
        cases tail with
        | nil => simp at length
        | cons i tail =>
          cases tail with
          | nil => simp at length
          | cons p rest =>
            cases rest with
            | nil => exact ⟨v, i, p, rfl⟩
            | cons q rest => simp at length
    obtain ⟨sourceValue, sourceIndex, sourcePointer, rfl⟩ := three
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | cons indexRel tail =>
        cases tail with
        | cons pointerRel tail =>
          cases tail with
          | nil =>
            rename_i flatValue flatIndex flatPointer
            obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
            have successful : doApp (nextSource.refs, nextSource.ffi) .aw8updateUnsafe [sourcePointer, sourceIndex, sourceValue] ≠ none := by
              intro failed
              apply safe nextSource
              change EvaluateHOL.evaluate source sourceEnv [.app .aw8updateUnsafe [left, right, third]] = _
              rw [EvaluateHOL.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
              rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
              simp [getOpClass, failed, EvaluateHOL.typeError]
            obtain ⟨flag, address, index, byte, values, rfl, rfl, rfl, lookup⟩ :=
              aw8update_operands nextSource sourcePointer sourceIndex sourceValue true successful
            have flatLocation := (valueRel_location_iff nextGenv flag address flatPointer).mp pointerRel
            have flatIndexEq := (valueRel_literal_iff nextGenv (.intLit index) flatIndex).mp indexRel
            have flatValueEq := (valueRel_literal_iff nextGenv (.word8 byte) flatValue).mp valueRel
            subst flatPointer
            subst flatIndex
            subst flatValue
            have primitive := aw8update_complete_related nextGenv nextSource nextFlat states nextInvariant.1
              flag address values lookup index byte true
            simp only [if_true] at primitive
            cases sourceApp : doApp (nextSource.refs, nextSource.ffi) .aw8updateUnsafe
                [.loc flag address, .litv (.intLit index), .litv (.word8 byte)] with
            | none => exact (successful sourceApp).elim
            | some sourceOut =>
              cases sourceOut with
              | mk store sourceResult =>
                cases store with
                | mk refs ffi =>
                  cases flatApp : FlatSem.doAppMemory nextFlat .aw8updateUnsafe
                      [.loc flag (address + 1), .litv (.intLit index), .litv (.word8 byte)] with
                  | none => simp [sourceApp, flatApp] at primitive
                  | some flatOut =>
                    cases flatOut with
                    | none => simp [sourceApp, flatApp] at primitive
                    | some flatOut =>
                      cases flatOut with
                      | mk flatAfter flatResult =>
                        simp only [sourceApp, flatApp] at primitive
                        obtain ⟨rfl, flatEq, stateRel, reserved, resultRel⟩ := primitive
                        have finalInvariant := factoredInvariant_changeStores interp transform gen nextGenv (start, finish, other)
                          nextSource nextFlat refs flatAfter.refs nextInvariant (by rw [flatEq] at stateRel; exact stateRel) reserved
                        have finalInvariant' : factoredInvariant interp transform gen nextGenv (start, finish, other)
                            { nextSource with refs := refs } flatAfter := by
                          rw [flatEq]
                          exact finalInvariant
                        refine ⟨nextGenv, ?_, ?_⟩
                        · unfold ExprSim
                          rw [EvaluateHOL.evaluate]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
                          simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                          rw [FlatSem.evaluate]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                          rw [(FlatSem.fixClock_evaluations flatEnv flat
                            [compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
                            (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                            getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp,
                            FlatSem.doAppNumeric, flatApp]
                          cases resultRel with
                          | value valueRel => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.value (.cons valueRel .nil)) stateRel
                          | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.raise valueRel) stateRel
                          | abort error => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.abort error) stateRel
                        · rw [EvaluateHOL.evaluate]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
                          simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                          rw [FlatSem.evaluate]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                          rw [(FlatSem.fixClock_evaluations flatEnv flat
                            [compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
                            (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                            getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp,
                            FlatSem.doAppNumeric, flatApp]
                          cases resultRel with
                          | value valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro finalInvariant' (And.intro nextGeneration forward))
                          | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro finalInvariant' (And.intro nextGeneration forward))
                          | abort error => simp [EvaluateHOL.listResult]


end Flapjack.Compiler.Backend.SourceToFlat
