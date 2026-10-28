import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBoundedArray

/-! Bounded vector and string primitive simulation over preliminary relations. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- A successful string subscript has string and integer operands. -/
theorem strsub_operands {F : Type} (source : State F) (string index : Value)
    (successful : doApp (source.refs, source.ffi) .strsub [string, index] ≠ none) :
    ∃ str n, string = .litv (.strLit str) ∧ index = .litv (.intLit n) := by
  cases string <;> cases index <;> simp [doApp, doAppNumericCore, doAppBasic] at successful
  case litv.litv strLit intLit =>
    cases strLit <;> cases intLit <;> simp at successful
    case strLit.intLit str n => exact ⟨str, n, rfl, rfl⟩

/-- String subscripting yields related characters or related bounds exceptions. -/
theorem strsub_complete_related {C F : Type} (genv : GlobalEnv)
    (source : State F) (flat : FlatSem.State C F) (ok : genvCOk genv.c)
    (str : Flapjack.Basis.Pure.MlString.MlString) (index : Int) :
    match doApp (source.refs, source.ffi) .strsub [.litv (.strLit str), .litv (.intLit index)],
      FlatSem.doAppData flat .strsub [.litv (.strLit str), .litv (.intLit index)] with
    | some ((refs, ffi), result), some (some (nextFlat, flatResult)) =>
        refs = source.refs ∧ ffi = source.ffi ∧ nextFlat = flat ∧ ResultRel ValueRel genv result flatResult
    | _, _ => False := by
  have exceptionRel := (exceptionValues_related genv ok).2.2.2
  by_cases negative : index < 0
  · simp [doApp, doAppNumericCore, doAppBasic, FlatSem.doAppData, SemanticPrimitivesHOL.readIndexed,
      FlatSem.readIndexed, SemanticPrimitivesHOL.boundsFailure, FlatSem.boundsFailure, negative, ResultRel.raise exceptionRel]
  · cases element : str.explode[index.toNat]? with
    | none => simp [doApp, doAppNumericCore, doAppBasic, FlatSem.doAppData, SemanticPrimitivesHOL.readIndexed,
        FlatSem.readIndexed, SemanticPrimitivesHOL.boundsFailure, FlatSem.boundsFailure, negative, element, ResultRel.raise exceptionRel]
    | some char => simp [doApp, doAppNumericCore, doAppBasic, FlatSem.doAppData, SemanticPrimitivesHOL.readIndexed,
        FlatSem.readIndexed, negative, element, ResultRel.value (ValueRel.literal genv (.char char))]

/-- A vector subscript without type error has vector and integer operands. -/
theorem vsub_operands {F : Type} (source : State F) (vector index : Value) (unsafeOp : Bool)
    (successful : doApp (source.refs, source.ffi) (if unsafeOp then .vsubUnsafe else .vsub) [vector, index] ≠ none) :
    ∃ values n, vector = .vectorv values ∧ index = .litv (.intLit n) := by
  cases unsafeOp <;> cases vector <;> cases index <;> simp [doApp, doAppNumericCore, doAppBasic] at successful
  all_goals rename_i values lit
  all_goals cases lit <;> simp at successful
  all_goals rename_i n
  all_goals exact ⟨values, n, rfl, rfl⟩

/-- Related vectors return related elements or agree on bounds behavior. -/
theorem vsub_complete_related {C F : Type} (genv : GlobalEnv)
    (source : State F) (flat : FlatSem.State C F) (ok : genvCOk genv.c)
    (values : List Value) (flatValues : List FlatSem.Value) (related : List.Forall₂ (ValueRel genv) values flatValues)
    (index : Int) (unsafeOp : Bool) :
    let op := if unsafeOp then Flapjack.AstHOL.Op.vsubUnsafe else .vsub
    match doApp (source.refs, source.ffi) op [.vectorv values, .litv (.intLit index)],
      FlatSem.doAppData flat op [.vectorv flatValues, .litv (.intLit index)] with
    | none, some none => True
    | some ((refs, ffi), result), some (some (nextFlat, flatResult)) =>
        refs = source.refs ∧ ffi = source.ffi ∧ nextFlat = flat ∧ ResultRel ValueRel genv result flatResult
    | _, _ => False := by
  have exceptionRel := (exceptionValues_related genv ok).2.2.2
  have pairRel := forall₂_lookupRel related index.toNat
  by_cases negative : index < 0
  · cases unsafeOp <;> simp [doApp, doAppNumericCore, doAppBasic, FlatSem.doAppData,
      SemanticPrimitivesHOL.readIndexed, FlatSem.readIndexed, SemanticPrimitivesHOL.boundsFailure,
      FlatSem.boundsFailure, negative, ResultRel.raise exceptionRel]
  · cases src : values[index.toNat]? with
    | none =>
      cases dst : flatValues[index.toNat]? with
      | none => cases unsafeOp <;> simp [doApp, doAppNumericCore, doAppBasic, FlatSem.doAppData,
          SemanticPrimitivesHOL.readIndexed, FlatSem.readIndexed, SemanticPrimitivesHOL.boundsFailure,
          FlatSem.boundsFailure, negative, src, dst, ResultRel.raise exceptionRel]
      | some value => simp [src, dst, LookupRel] at pairRel
    | some value =>
      cases dst : flatValues[index.toNat]? with
      | none => simp [src, dst, LookupRel] at pairRel
      | some flatValue =>
        simp only [src, dst, LookupRel] at pairRel
        cases unsafeOp <;> simp [doApp, doAppNumericCore, doAppBasic, FlatSem.doAppData,
          SemanticPrimitivesHOL.readIndexed, FlatSem.readIndexed, negative, src, dst, ResultRel.value pairRel]

/-- A string length operation without a type error has a string operand. -/
theorem strlen_operand {F : Type} (source : State F) (operand : Value)
    (successful : doApp (source.refs, source.ffi) .strlen [operand] ≠ none) :
    ∃ str, operand = .litv (.strLit str) := by
  cases operand <;> simp [doApp, doAppNumericCore, doAppBasic] at successful
  case litv lit =>
    cases lit <;> simp at successful
    case strLit str => exact ⟨str, rfl⟩

/-- A vector length operation without a type error has a vector operand. -/
theorem vlength_operand {F : Type} (source : State F) (operand : Value)
    (successful : doApp (source.refs, source.ffi) .vlength [operand] ≠ none) :
    ∃ values, operand = .vectorv values := by
  cases operand <;> simp [doApp, doAppNumericCore, doAppBasic] at successful
  case vectorv values => exact ⟨values, rfl⟩

/-- strlen expressions compose a growing operand simulation in a local environment. -/
theorem localEnvBounded_strlen {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .strlen [body]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have bodySafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .strlen [body]] = _
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
        have successful : doApp (nextSource.refs, nextSource.ffi) .strlen [operand] ≠ none := by
          intro failed
          apply safe nextSource
          change EvaluateHOL.evaluate source sourceEnv [.app .strlen [body]] = _
          rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp [getOpClass, failed, EvaluateHOL.typeError]
        obtain ⟨str, rfl⟩ := strlen_operand nextSource operand successful
        have flatEq := (valueRel_literal_iff nextGenv (.strLit str) flatOperand).mp valueRel
        subst flatOperand
        have resultRel : ValueRel nextGenv (.litv (.intLit str.explode.length)) (.litv (.intLit str.explode.length)) :=
          .literal nextGenv _
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
          simp [getOpClass, doApp, doAppNumericCore, doAppBasic, astOpToFlatOp,
            FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, EvaluateHOL.listResult]
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
          simpa [getOpClass, doApp, doAppNumericCore, doAppBasic, astOpToFlatOp,
            FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, EvaluateHOL.listResult] using
            And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))


/-- vlength expressions compose a growing operand simulation in a local environment. -/
theorem localEnvBounded_vlength {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .vlength [body]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have bodySafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .vlength [body]] = _
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
        have successful : doApp (nextSource.refs, nextSource.ffi) .vlength [operand] ≠ none := by
          intro failed
          apply safe nextSource
          change EvaluateHOL.evaluate source sourceEnv [.app .vlength [body]] = _
          rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp [getOpClass, failed, EvaluateHOL.typeError]
        obtain ⟨values, rfl⟩ := vlength_operand nextSource operand successful
        obtain ⟨flatValues, rfl, relatedValues⟩ := (valueRel_vector_iff nextGenv values flatOperand).mp valueRel
        have sameLength := relatedValues.length_eq
        have resultRel : ValueRel nextGenv (.litv (.intLit values.length)) (.litv (.intLit values.length)) :=
          .literal nextGenv _
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
          simp [getOpClass, doApp, doAppNumericCore, doAppBasic, astOpToFlatOp,
            FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, ← sameLength, EvaluateHOL.listResult]
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
          simpa [getOpClass, doApp, doAppNumericCore, doAppBasic, astOpToFlatOp,
            FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, ← sameLength, EvaluateHOL.listResult] using
            And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))


/-- Compose vsub operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_vsub {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .vsub [left, right]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .vsub [left, right]] = _
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
          have successful : doApp (nextSource.refs, nextSource.ffi) .vsub [sourceSize, sourceValue] ≠ none := by
            intro failed
            apply safe nextSource
            change EvaluateHOL.evaluate source sourceEnv [.app .vsub [left, right]] = _
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp [getOpClass, failed, EvaluateHOL.typeError]
          obtain ⟨values, index, rfl, rfl⟩ := vsub_operands nextSource sourceSize sourceValue false successful
          obtain ⟨flatValues, rfl, relatedValues⟩ := (valueRel_vector_iff nextGenv values flatSize).mp sizeRel
          have flatIndex := (valueRel_literal_iff nextGenv (.intLit index) flatValue).mp valueRel
          subst flatValue
          have primitive := vsub_complete_related nextGenv nextSource nextFlat nextInvariant.1 values flatValues relatedValues index false
          simp only [Bool.false_eq_true, if_false] at primitive
          cases sourceApp : doApp (nextSource.refs, nextSource.ffi) .vsub
              [.vectorv values, .litv (.intLit index)] with
          | none => exact (successful sourceApp).elim
          | some sourceOut =>
            cases sourceOut with
            | mk store sourceResult =>
              cases store with
              | mk refs ffi =>
                cases flatApp : FlatSem.doAppData nextFlat .vsub
                    [.vectorv flatValues, .litv (.intLit index)] with
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
                          FlatSem.doAppNumeric, FlatSem.doAppMemory, flatApp]
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
                          FlatSem.doAppNumeric, FlatSem.doAppMemory, flatApp]
                        cases resultRel with
                        | value valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))
                        | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))
                        | abort error => simp [EvaluateHOL.listResult]

/-- Compose vsubUnsafe operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_vsubUnsafe {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .vsubUnsafe [left, right]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .vsubUnsafe [left, right]] = _
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
          have successful : doApp (nextSource.refs, nextSource.ffi) .vsubUnsafe [sourceSize, sourceValue] ≠ none := by
            intro failed
            apply safe nextSource
            change EvaluateHOL.evaluate source sourceEnv [.app .vsubUnsafe [left, right]] = _
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp [getOpClass, failed, EvaluateHOL.typeError]
          obtain ⟨values, index, rfl, rfl⟩ := vsub_operands nextSource sourceSize sourceValue true successful
          obtain ⟨flatValues, rfl, relatedValues⟩ := (valueRel_vector_iff nextGenv values flatSize).mp sizeRel
          have flatIndex := (valueRel_literal_iff nextGenv (.intLit index) flatValue).mp valueRel
          subst flatValue
          have primitive := vsub_complete_related nextGenv nextSource nextFlat nextInvariant.1 values flatValues relatedValues index true
          simp only [if_true] at primitive
          cases sourceApp : doApp (nextSource.refs, nextSource.ffi) .vsubUnsafe
              [.vectorv values, .litv (.intLit index)] with
          | none => exact (successful sourceApp).elim
          | some sourceOut =>
            cases sourceOut with
            | mk store sourceResult =>
              cases store with
              | mk refs ffi =>
                cases flatApp : FlatSem.doAppData nextFlat .vsubUnsafe
                    [.vectorv flatValues, .litv (.intLit index)] with
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
                          FlatSem.doAppNumeric, FlatSem.doAppMemory, flatApp]
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
                          FlatSem.doAppNumeric, FlatSem.doAppMemory, flatApp]
                        cases resultRel with
                        | value valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))
                        | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))
                        | abort error => simp [EvaluateHOL.listResult]

/-- Compose strsub operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_strsub {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .strsub [left, right]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .strsub [left, right]] = _
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
          have successful : doApp (nextSource.refs, nextSource.ffi) .strsub [sourceSize, sourceValue] ≠ none := by
            intro failed
            apply safe nextSource
            change EvaluateHOL.evaluate source sourceEnv [.app .strsub [left, right]] = _
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp [getOpClass, failed, EvaluateHOL.typeError]
          obtain ⟨str, index, rfl, rfl⟩ := strsub_operands nextSource sourceSize sourceValue successful
          have flatString := (valueRel_literal_iff nextGenv (.strLit str) flatSize).mp sizeRel
          have flatIndex := (valueRel_literal_iff nextGenv (.intLit index) flatValue).mp valueRel
          subst flatSize
          subst flatValue
          have primitive := strsub_complete_related nextGenv nextSource nextFlat nextInvariant.1 str index
          cases sourceApp : doApp (nextSource.refs, nextSource.ffi) .strsub
              [.litv (.strLit str), .litv (.intLit index)] with
          | none => exact (successful sourceApp).elim
          | some sourceOut =>
            cases sourceOut with
            | mk store sourceResult =>
              cases store with
              | mk refs ffi =>
                cases flatApp : FlatSem.doAppData nextFlat .strsub
                    [.litv (.strLit str), .litv (.intLit index)] with
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
                          FlatSem.doAppNumeric, FlatSem.doAppMemory, flatApp]
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
                          FlatSem.doAppNumeric, FlatSem.doAppMemory, flatApp]
                        cases resultRel with
                        | value valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))
                        | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))
                        | abort error => simp [EvaluateHOL.listResult]


end Flapjack.Compiler.Backend.SourceToFlat
