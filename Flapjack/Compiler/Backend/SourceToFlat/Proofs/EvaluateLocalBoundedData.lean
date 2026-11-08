import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ThunkRel
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBoundedArray
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ListConversion
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PrimitiveData

/-! Bounded vector and string primitive simulation over preliminary relations. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

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
    obtain ⟨operand, rfl⟩ := EvaluateProps.evaluateSingFull source sourceEnv body nextSource sourceValues sourceRun
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


/-- vfromList expressions compose a growing operand simulation in a local environment. -/
theorem localEnvBounded_vfromList {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .vfromList [body]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have bodySafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .vfromList [body]] = _
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
    obtain ⟨operand, rfl⟩ := EvaluateProps.evaluateSingFull source sourceEnv body nextSource sourceValues sourceRun
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | nil =>
        rename_i flatOperand
        obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
        have successful : doApp (nextSource.refs, nextSource.ffi) .vfromList [operand] ≠ none := by
          intro failed
          apply safe nextSource
          change EvaluateHOL.evaluate source sourceEnv [.app .vfromList [body]] = _
          rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp [getOpClass, failed, EvaluateHOL.typeError]
        have sourceDecode : ∃ values, valueToList operand = some values := by
          cases decoded : valueToList operand with
          | none => simp [doApp, doAppNumericCore, doAppBasic, decoded] at successful
          | some values => exact ⟨values, rfl⟩
        obtain ⟨values, decoded⟩ := sourceDecode
        obtain ⟨flatValues, flatDecoded, relatedValues⟩ := valueToList_related nextGenv nextInvariant.1 operand flatOperand values ⟨valueRel, decoded⟩
        have resultRel : ValueRel nextGenv (.vectorv values) (.vectorv flatValues) :=
          valueRel_vector nextGenv values flatValues relatedValues
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
            FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, decoded, flatDecoded, EvaluateHOL.listResult]
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
            FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, decoded, flatDecoded, EvaluateHOL.listResult] using
            And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))


/-- strcat expressions compose a growing operand simulation in a local environment. -/
theorem localEnvBounded_strcat {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .strcat [body]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have bodySafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .strcat [body]] = _
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
    obtain ⟨operand, rfl⟩ := EvaluateProps.evaluateSingFull source sourceEnv body nextSource sourceValues sourceRun
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | nil =>
        rename_i flatOperand
        obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
        have successful : doApp (nextSource.refs, nextSource.ffi) .strcat [operand] ≠ none := by
          intro failed
          apply safe nextSource
          change EvaluateHOL.evaluate source sourceEnv [.app .strcat [body]] = _
          rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp [getOpClass, failed, EvaluateHOL.typeError]
        have sourceDecode : ∃ values, valueToList operand = some values := by
          cases decoded : valueToList operand with
          | none => simp [doApp, doAppNumericCore, doAppBasic, decoded] at successful
          | some values => exact ⟨values, rfl⟩
        obtain ⟨values, decoded⟩ := sourceDecode
        obtain ⟨flatValues, flatDecoded, relatedValues⟩ := valueToList_related nextGenv nextInvariant.1 operand flatOperand values ⟨valueRel, decoded⟩
        have stringDecode : ∃ str, valuesToString values = some str := by
          cases result : valuesToString values with
          | none => simp [doApp, doAppNumericCore, doAppBasic, decoded, result] at successful
          | some str => exact ⟨str, rfl⟩
        obtain ⟨str, stringDecoded⟩ := stringDecode
        have flatStringDecoded := valuesToString_related nextGenv values flatValues str relatedValues stringDecoded
        have resultRel : ValueRel nextGenv (.litv (.strLit str)) (.litv (.strLit str)) := .literal nextGenv _
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
            FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, decoded, flatDecoded, stringDecoded, flatStringDecoded, EvaluateHOL.listResult]
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
            FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, decoded, flatDecoded, stringDecoded, flatStringDecoded, EvaluateHOL.listResult] using
            And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))


/-- implode expressions compose a growing operand simulation in a local environment. -/
theorem localEnvBounded_implode {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .implode [body]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have bodySafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .implode [body]] = _
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
    obtain ⟨operand, rfl⟩ := EvaluateProps.evaluateSingFull source sourceEnv body nextSource sourceValues sourceRun
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | nil =>
        rename_i flatOperand
        obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
        have successful : doApp (nextSource.refs, nextSource.ffi) .implode [operand] ≠ none := by
          intro failed
          apply safe nextSource
          change EvaluateHOL.evaluate source sourceEnv [.app .implode [body]] = _
          rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp [getOpClass, failed, EvaluateHOL.typeError]
        have sourceDecode : ∃ chars, valueToCharList operand = some chars := by
          cases decoded : valueToCharList operand with
          | none => simp [doApp, doAppNumericCore, doAppBasic, decoded] at successful
          | some chars => exact ⟨chars, rfl⟩
        obtain ⟨chars, decoded⟩ := sourceDecode
        have flatDecoded := valueToCharList_related nextGenv nextInvariant.1 operand flatOperand chars ⟨valueRel, decoded⟩
        have resultRel : ValueRel nextGenv (.litv (.strLit (.implode chars))) (.litv (.strLit (.implode chars))) :=
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
            FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, decoded, flatDecoded, EvaluateHOL.listResult]
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
            FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, decoded, flatDecoded, EvaluateHOL.listResult] using
            And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))


/-- explode expressions compose a growing operand simulation in a local environment. -/
theorem localEnvBounded_explode {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .explode [body]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have bodySafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .explode [body]] = _
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
    obtain ⟨operand, rfl⟩ := EvaluateProps.evaluateSingFull source sourceEnv body nextSource sourceValues sourceRun
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | nil =>
        rename_i flatOperand
        obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
        have successful : doApp (nextSource.refs, nextSource.ffi) .explode [operand] ≠ none := by
          intro failed
          apply safe nextSource
          change EvaluateHOL.evaluate source sourceEnv [.app .explode [body]] = _
          rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp [getOpClass, failed, EvaluateHOL.typeError]
        have stringOperand : ∃ str, operand = .litv (.strLit str) := by
          cases operand <;> simp [doApp, doAppNumericCore, doAppBasic] at successful
          case litv lit =>
            cases lit <;> simp at successful
            case strLit str => exact ⟨str, rfl⟩
        obtain ⟨str, rfl⟩ := stringOperand
        have flatEq := (valueRel_literal_iff nextGenv (.strLit str) flatOperand).mp valueRel
        subst flatOperand
        have itemsRel : List.Forall₂ (ValueRel nextGenv) (str.explode.map (Value.litv ∘ Lit.char))
            (str.explode.map (FlatSem.Value.litv ∘ Lit.char)) := by
          induction str.explode with
          | nil => exact .nil
          | cons char rest ih => exact .cons (.literal nextGenv (.char char)) ih
        have resultRel := listToValue_related nextGenv _ _ ⟨nextInvariant.1.2.2.1, itemsRel⟩
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
    obtain ⟨operand, rfl⟩ := EvaluateProps.evaluateSingFull source sourceEnv body nextSource sourceValues sourceRun
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


/-- Compose listAppend operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_listAppend {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .listAppend [left, right]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .listAppend [left, right]] = _
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
          have successful : doApp (nextSource.refs, nextSource.ffi) .listAppend [sourceSize, sourceValue] ≠ none := by
            intro failed
            apply safe nextSource
            change EvaluateHOL.evaluate source sourceEnv [.app .listAppend [left, right]] = _
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp [getOpClass, failed, EvaluateHOL.typeError]
          have leftDecoded : ∃ values, valueToList sourceSize = some values := by
            cases decoded : valueToList sourceSize with
            | none => simp [doApp, doAppNumericCore, doAppBasic, decoded] at successful
            | some values => exact ⟨values, rfl⟩
          obtain ⟨leftValues, leftDecoded⟩ := leftDecoded
          have rightDecoded : ∃ values, valueToList sourceValue = some values := by
            cases decoded : valueToList sourceValue with
            | none => simp [doApp, doAppNumericCore, doAppBasic, leftDecoded, decoded] at successful
            | some values => exact ⟨values, rfl⟩
          obtain ⟨rightValues, rightDecoded⟩ := rightDecoded
          obtain ⟨flatLeft, flatLeftDecoded, leftRel⟩ := valueToList_related nextGenv nextInvariant.1 sourceSize flatSize leftValues ⟨sizeRel, leftDecoded⟩
          obtain ⟨flatRight, flatRightDecoded, rightRel⟩ := valueToList_related nextGenv nextInvariant.1 sourceValue flatValue rightValues ⟨valueRel, rightDecoded⟩
          have appendedRel : List.Forall₂ (ValueRel nextGenv) (leftValues ++ rightValues) (flatLeft ++ flatRight) := by
            clear leftDecoded flatLeftDecoded
            induction leftRel with
            | nil => exact rightRel
            | cons head _ ih => exact .cons head ih
          have resultRel := listToValue_related nextGenv _ _ ⟨nextInvariant.1.2.2.1, appendedRel⟩
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
            simp [getOpClass, doApp, doAppNumericCore, doAppBasic, leftDecoded, rightDecoded, astOpToFlatOp,
              FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData,
              flatLeftDecoded, flatRightDecoded, EvaluateHOL.listResult]
            exact ⟨.value (.cons resultRel .nil), states⟩
          · rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
            rw [FlatSem.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap right, compileExp trace compMap left]
              (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
            simpa [getOpClass, doApp, doAppNumericCore, doAppBasic, leftDecoded, rightDecoded, astOpToFlatOp,
              FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData,
              flatLeftDecoded, flatRightDecoded, EvaluateHOL.listResult] using
              And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))


/-- Compose configGC operand hypotheses in an arbitrary local environment. -/
theorem localEnvBounded_configGC {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .configGC [left, right]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .configGC [left, right]] = _
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
          have successful : doApp (nextSource.refs, nextSource.ffi) .configGC [sourceSize, sourceValue] ≠ none := by
            intro failed
            apply safe nextSource
            change EvaluateHOL.evaluate source sourceEnv [.app .configGC [left, right]] = _
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp [getOpClass, failed, EvaluateHOL.typeError]
          cases sizeRel <;> cases valueRel <;> simp_all [doApp, doAppNumericCore, doAppBasic]
          rename_i firstLit secondLit
          cases firstLit <;> cases secondLit <;> simp_all
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
            simp [getOpClass, doApp, doAppNumericCore, doAppBasic, astOpToFlatOp,
              FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData,
              FlatSem.unitValue, EvaluateHOL.listResult]
            exact ⟨.value (.cons (.tuple nextGenv [] [] (.nil nextGenv)) .nil), states⟩
          · rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
            rw [FlatSem.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap right, compileExp trace compMap left]
              (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
            simpa [getOpClass, doApp, doAppNumericCore, doAppBasic, astOpToFlatOp,
              FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData,
              FlatSem.unitValue, EvaluateHOL.listResult] using
              And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))


/-- The environment-ID operation leaves any related, well-formed operand
unchanged; source environment values themselves have no related flat value in
the factored value relation. -/
theorem envId_related_identity {F : Type} (genv : GlobalEnv) (source : State F)
    (value : Value) (flatValue : FlatSem.Value) (related : ValueRel genv value flatValue)
    (successful : doApp (source.refs, source.ffi) .envId [value] ≠ none) :
    doApp (source.refs, source.ffi) .envId [value] = some ((source.refs, source.ffi), .val value) := by
  cases related <;> simp [doApp, doAppNumericCore, doAppBasic] at successful ⊢
  case tuple sources flats h =>
    cases sources with
    | nil => simp at successful
    | cons first tail =>
      cases tail with
      | nil => simp at successful
      | cons second rest =>
        cases rest with
        | nil => rfl
        | cons third rest => simp at successful

/-- Environment-ID applications compose operand simulations in a local environment. -/
theorem localEnvBounded_envId {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp) (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .envId [body]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have bodySafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .envId [body]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, bad]
  obtain ⟨nextGenv, bodySim, post⟩ := bodyIH genv start finish other source flat baseEnv sourceLocal flatEnv traces
    trace baseMap gen clockBound localRel envInv tracesLen invariant generation bodySafe
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
      rw [flatRun]
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
      rw [flatRun]
      exact ⟨.raise valueRel, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [flatRun]
      exact post
  | @value sourceValues flatValues valuesRel =>
    obtain ⟨value, rfl⟩ := EvaluateProps.evaluateSingFull source sourceEnv body nextSource sourceValues sourceRun
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | nil =>
        rename_i flatValue
        obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
        have successful : doApp (nextSource.refs, nextSource.ffi) .envId [value] ≠ none := by
          intro failed
          apply safe nextSource
          change EvaluateHOL.evaluate source sourceEnv [.app .envId [body]] = _
          rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp [getOpClass, failed, EvaluateHOL.typeError]
        have sourceApp := envId_related_identity nextGenv nextSource value flatValue valueRel successful
        refine ⟨nextGenv, ?_, ?_⟩
        · unfold ExprSim
          rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
          rw [flatRun]
          simp [getOpClass, sourceApp, EvaluateHOL.listResult]
          exact ⟨.value (.cons valueRel .nil), states⟩
        · rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
          rw [flatRun]
          simpa [getOpClass, sourceApp, EvaluateHOL.listResult] using
            And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))

/-- String slicing composes operand simulations in a local environment. -/
theorem localEnvBounded_copyStrStr {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right third : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right)
    (thirdIH : LocalEnvBoundedIH (F := F) interp transform limit third) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .copyStrStr [left, right, third]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [third, right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .copyStrStr [left, right, third]] = _
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
            have successful : doApp (nextSource.refs, nextSource.ffi) .copyStrStr [sourcePointer, sourceIndex, sourceValue] ≠ none := by
              intro failed
              apply safe nextSource
              change EvaluateHOL.evaluate source sourceEnv [.app .copyStrStr [left, right, third]] = _
              rw [EvaluateHOL.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
              rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
              simp [getOpClass, failed, EvaluateHOL.typeError]
            obtain ⟨text, offset, sliceLength, rfl, rfl, rfl⟩ :=
              copyStrStr_operands nextSource sourcePointer sourceIndex sourceValue successful
            have flatText := (valueRel_literal_iff nextGenv (.strLit text) flatPointer).mp pointerRel
            have flatOffset := (valueRel_literal_iff nextGenv (.intLit offset) flatIndex).mp indexRel
            have flatLength := (valueRel_literal_iff nextGenv (.intLit sliceLength) flatValue).mp valueRel
            subst flatPointer
            subst flatIndex
            subst flatValue
            have primitive := copyStrStr_complete_related nextGenv nextSource nextFlat nextInvariant.1 text offset sliceLength
            cases sourceApp : doApp (nextSource.refs, nextSource.ffi) .copyStrStr
                [.litv (.strLit text), .litv (.intLit offset), .litv (.intLit sliceLength)] with
            | none => exact (successful sourceApp).elim
            | some sourceOut =>
              cases sourceOut with
              | mk store sourceResult =>
                cases store with
                | mk refs ffi =>
                  cases flatApp : FlatSem.doAppCopy nextFlat .copyStrStr
                      [.litv (.strLit text), .litv (.intLit offset), .litv (.intLit sliceLength)] with
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
                          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
                          simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                          rw [FlatSem.evaluate]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                          rw [(FlatSem.fixClock_evaluations flatEnv flat
                            [compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
                            (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                            getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp,
                            FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, flatApp]
                          cases resultRel with
                          | value valueRel => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.value (.cons valueRel .nil)) states
                          | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.raise valueRel) states
                          | abort error => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.abort error) states
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
                            FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, flatApp]
                          cases resultRel with
                          | value valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))
                          | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))
                          | abort error => simp [EvaluateHOL.listResult]

/-- Fused multiply-add composes bounded operand simulations. -/
theorem localEnvBounded_floatFma {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right third : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right)
    (thirdIH : LocalEnvBoundedIH (F := F) interp transform limit third) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.arith .fma .float64T) [left, right, third]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [third, right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app (.arith .fma .float64T) [left, right, third]] = _
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
            have successful : doApp (nextSource.refs, nextSource.ffi) (.arith .fma .float64T) [sourcePointer, sourceIndex, sourceValue] ≠ none := by
              intro failed
              apply safe nextSource
              change EvaluateHOL.evaluate source sourceEnv [.app (.arith .fma .float64T) [left, right, third]] = _
              rw [EvaluateHOL.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
              rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
              simp [getOpClass, failed, EvaluateHOL.typeError]
            obtain ⟨text, offset, sliceLength, rfl, rfl, rfl⟩ :=
              floatFma_operands nextSource sourcePointer sourceIndex sourceValue successful
            have flatText := (valueRel_literal_iff nextGenv (.float64 text) flatPointer).mp pointerRel
            have flatOffset := (valueRel_literal_iff nextGenv (.float64 offset) flatIndex).mp indexRel
            have flatLength := (valueRel_literal_iff nextGenv (.float64 sliceLength) flatValue).mp valueRel
            subst flatPointer
            subst flatIndex
            subst flatValue
            have primitive := floatFma_related nextGenv nextSource nextFlat text offset sliceLength
            cases sourceApp : doApp (nextSource.refs, nextSource.ffi) (.arith .fma .float64T)
                [.litv (.float64 text), .litv (.float64 offset), .litv (.float64 sliceLength)] with
            | none => exact (successful sourceApp).elim
            | some sourceOut =>
              cases sourceOut with
              | mk store sourceResult =>
                cases store with
                | mk refs ffi =>
                  cases flatApp : FlatSem.doAppNumeric nextFlat (.arith .fma .float64T)
                      [.litv (.float64 text), .litv (.float64 offset), .litv (.float64 sliceLength)] with
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
                          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
                          simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                          rw [FlatSem.evaluate]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                          rw [(FlatSem.fixClock_evaluations flatEnv flat
                            [compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
                            (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                            getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp,
                            flatApp]
                          cases resultRel with
                          | value valueRel => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.value (.cons valueRel .nil)) states
                          | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.raise valueRel) states
                          | abort error => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.abort error) states
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
                            flatApp]
                          cases resultRel with
                          | value valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))
                          | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))
                          | abort error => simp [EvaluateHOL.listResult]

/-- Byte-array slicing composes operand simulations in a local environment. -/
theorem localEnvBounded_copyAw8Str {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right third : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right)
    (thirdIH : LocalEnvBoundedIH (F := F) interp transform limit third) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .copyAw8Str [left, right, third]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [third, right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .copyAw8Str [left, right, third]] = _
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
            have successful : doApp (nextSource.refs, nextSource.ffi) .copyAw8Str [sourcePointer, sourceIndex, sourceValue] ≠ none := by
              intro failed
              apply safe nextSource
              change EvaluateHOL.evaluate source sourceEnv [.app .copyAw8Str [left, right, third]] = _
              rw [EvaluateHOL.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
              rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
              simp [getOpClass, failed, EvaluateHOL.typeError]
            obtain ⟨flag, address, offset, sliceLength, bytes, rfl, rfl, rfl, lookup⟩ :=
              copyAw8Str_operands nextSource sourcePointer sourceIndex sourceValue successful
            have flatLocation := (valueRel_location_iff nextGenv flag address flatPointer).mp pointerRel
            have flatOffset := (valueRel_literal_iff nextGenv (.intLit offset) flatIndex).mp indexRel
            have flatLength := (valueRel_literal_iff nextGenv (.intLit sliceLength) flatValue).mp valueRel
            subst flatPointer
            subst flatIndex
            subst flatValue
            have primitive := copyAw8Str_complete_related nextGenv nextSource nextFlat states nextInvariant.1 flag address bytes lookup offset sliceLength
            cases sourceApp : doApp (nextSource.refs, nextSource.ffi) .copyAw8Str
                [.loc flag address, .litv (.intLit offset), .litv (.intLit sliceLength)] with
            | none => exact (successful sourceApp).elim
            | some sourceOut =>
              cases sourceOut with
              | mk store sourceResult =>
                cases store with
                | mk refs ffi =>
                  cases flatApp : FlatSem.doAppCopy nextFlat .copyAw8Str
                      [.loc flag (address + 1), .litv (.intLit offset), .litv (.intLit sliceLength)] with
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
                          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [third, right, left] []).1, sourceRun]
                          simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                          rw [FlatSem.evaluate]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                          rw [(FlatSem.fixClock_evaluations flatEnv flat
                            [compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
                            (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                            getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp,
                            FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, flatApp]
                          cases resultRel with
                          | value valueRel => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.value (.cons valueRel .nil)) states
                          | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.raise valueRel) states
                          | abort error => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.abort error) states
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
                            FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, flatApp]
                          cases resultRel with
                          | value valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))
                          | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro nextInvariant (And.intro nextGeneration forward))
                          | abort error => simp [EvaluateHOL.listResult]

/-- Byte-array XOR preserves related stores in arbitrary local environments. -/
theorem localEnvBounded_xorAw8StrUnsafe {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .xorAw8StrUnsafe [left, right]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .xorAw8StrUnsafe [left, right]] = _
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
          have successful : doApp (nextSource.refs, nextSource.ffi) .xorAw8StrUnsafe [sourceSize, sourceValue] ≠ none := by
            intro failed
            apply safe nextSource
            change EvaluateHOL.evaluate source sourceEnv [.app .xorAw8StrUnsafe [left, right]] = _
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp [getOpClass, failed, EvaluateHOL.typeError]
          obtain ⟨flag, address, text, bytes, result, rfl, rfl, lookup, xor⟩ :=
            xorAw8Str_operands nextSource sourceSize sourceValue successful
          have flatLocation := (valueRel_location_iff nextGenv flag address flatSize).mp sizeRel
          have flatText := (valueRel_literal_iff nextGenv (.strLit text) flatValue).mp valueRel
          subst flatSize
          subst flatValue
          obtain ⟨sourceRefs, flatRefs, sourceApp, flatApp, stateRel, reserved⟩ :=
            xorAw8Str_related nextGenv nextSource nextFlat states flag address text bytes result lookup xor
          have finalInvariant := factoredInvariant_changeStores interp transform gen nextGenv (start, finish, other)
            nextSource nextFlat sourceRefs flatRefs nextInvariant stateRel reserved
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
            simp [getOpClass, sourceApp, astOpToFlatOp,
              FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, flatApp,
              FlatSem.unitValue, EvaluateHOL.listResult]
            exact ⟨.value (.cons (.tuple nextGenv [] [] (.nil nextGenv)) .nil), stateRel⟩
          · rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
            rw [FlatSem.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap right, compileExp trace compMap left]
              (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
            simpa [getOpClass, sourceApp, astOpToFlatOp,
              FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, flatApp,
              FlatSem.unitValue, EvaluateHOL.listResult] using
              And.intro growth (And.intro finalInvariant (And.intro nextGeneration forward))

/-- Thunk allocation composes the operand simulation with a related store allocation. -/
theorem localEnvBounded_allocThunk {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (mode : ThunkMode) (body : AstHOL.Exp)
    (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.thunkOp (.allocThunk mode)) [body]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have bodySafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app (.thunkOp (.allocThunk mode)) [body]] = _
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
    obtain ⟨operand, rfl⟩ := EvaluateProps.evaluateSingFull source sourceEnv body nextSource sourceValues sourceRun
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | nil =>
        rename_i flatOperand
        obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
        have successful : doApp (nextSource.refs, nextSource.ffi) (.thunkOp (.allocThunk mode)) [operand] ≠ none := by
          intro failed
          apply safe nextSource
          change EvaluateHOL.evaluate source sourceEnv [.app (.thunkOp (.allocThunk mode)) [body]] = _
          rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp [getOpClass, failed, EvaluateHOL.typeError]
        obtain ⟨sourceApp, flatApp, locationRel, stateRel, reserved⟩ :=
          allocThunk_related nextGenv nextSource nextFlat states mode operand flatOperand valueRel successful
        have finalInvariant := factoredInvariant_changeStores interp transform gen nextGenv (start, finish, other)
          nextSource nextFlat (storeAlloc (.thunk mode operand) nextSource.refs).1
          (storeAlloc (.thunk mode flatOperand) nextFlat.refs).1 nextInvariant stateRel reserved
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
          simp [getOpClass, sourceApp, astOpToFlatOp,
            FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, flatApp, EvaluateHOL.listResult]
          exact ⟨.value (.cons locationRel .nil), stateRel⟩
        · rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
          rw [FlatSem.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
            (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
          simpa [getOpClass, sourceApp, astOpToFlatOp,
            FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, flatApp, EvaluateHOL.listResult] using
            And.intro growth (And.intro finalInvariant (And.intro nextGeneration forward))

/-- Explicit thunk update preserves related stores in arbitrary local environments. -/
theorem localEnvBounded_updateThunk {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (mode : ThunkMode) (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.thunkOp (.updateThunk mode)) [left, right]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app (.thunkOp (.updateThunk mode)) [left, right]] = _
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
          have successful : doApp (nextSource.refs, nextSource.ffi) (.thunkOp (.updateThunk mode)) [sourceSize, sourceValue] ≠ none := by
            intro failed
            apply safe nextSource
            change EvaluateHOL.evaluate source sourceEnv [.app (.thunkOp (.updateThunk mode)) [left, right]] = _
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp [getOpClass, failed, EvaluateHOL.typeError]
          obtain ⟨address, sourceRefs, rfl, guard, assigned⟩ :=
            updateThunkOp_operands nextSource mode sourceSize sourceValue successful
          have flatLocation := (valueRel_location_iff nextGenv false address flatSize).mp sizeRel
          subst flatSize
          obtain ⟨flatRefs, sourceApp, flatApp, stateRel, reserved⟩ :=
            updateThunkOp_related nextGenv nextSource nextFlat states mode address sourceValue flatValue valueRel sourceRefs guard assigned
          have finalInvariant := factoredInvariant_changeStores interp transform gen nextGenv (start, finish, other)
            nextSource nextFlat sourceRefs flatRefs nextInvariant stateRel reserved
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
            simp [getOpClass, sourceApp, astOpToFlatOp,
              FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, flatApp,
              FlatSem.unitValue, EvaluateHOL.listResult]
            exact ⟨.value (.cons (.tuple nextGenv [] [] (.nil nextGenv)) .nil), stateRel⟩
          · rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
            rw [FlatSem.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap right, compileExp trace compMap left]
              (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
            simpa [getOpClass, sourceApp, astOpToFlatOp,
              FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, flatApp,
              FlatSem.unitValue, EvaluateHOL.listResult] using
              And.intro growth (And.intro finalInvariant (And.intro nextGeneration forward))

/-- String-to-byte-array copy composes operand simulations in a local environment. -/
theorem localEnvBounded_copyStrAw8 {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right third fourth fifth : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right)
    (thirdIH : LocalEnvBoundedIH (F := F) interp transform limit third)
    (fourthIH : LocalEnvBoundedIH (F := F) interp transform limit fourth)
    (fifthIH : LocalEnvBoundedIH (F := F) interp transform limit fifth) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .copyStrAw8 [left, right, third, fourth, fifth]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [fifth, fourth, third, right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .copyStrAw8 [left, right, third, fourth, fifth]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [fifth, fourth, third, right, left] []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform limit [fifth, fourth, third, right, left]
    (by intro expr member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl | rfl | rfl <;> assumption)
    genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
  unfold ExprListSim at argsSim
  simp only [compileExps] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [fifth, fourth, third, right, left] = sourceResult at argsSim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap fifth, compileExp trace compMap fourth, compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left] = flatResult at argsSim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := argsSim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [fifth, fourth, third, right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap fifth, compileExp trace compMap fourth, compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [fifth, fourth, third, right, left] []).1, sourceRun]
      trivial
  | raise valueRel =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [fifth, fourth, third, right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap fifth, compileExp trace compMap fourth, compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.raise valueRel, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [fifth, fourth, third, right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap fifth, compileExp trace compMap fourth, compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact post
  | @value sourceValues flatValues valuesRel =>
    have length := EvaluateProps.evaluateLengthFull source nextSource sourceEnv [fifth, fourth, third, right, left] sourceValues sourceRun
    have five : ∃ v5 v4 v3 v2 v1, sourceValues = [v5, v4, v3, v2, v1] := by
      cases sourceValues with
      | nil => simp at length
      | cons v5 tail =>
        cases tail with
        | nil => simp at length
        | cons v4 tail =>
          cases tail with
          | nil => simp at length
          | cons v3 tail =>
            cases tail with
            | nil => simp at length
            | cons v2 tail =>
              cases tail with
              | nil => simp at length
              | cons v1 rest =>
                cases rest with
                | nil => exact ⟨v5, v4, v3, v2, v1, rfl⟩
                | cons extra rest => simp at length
    obtain ⟨v5, v4, v3, v2, v1, rfl⟩ := five
    cases valuesRel with
    | cons r5 tail =>
      cases tail with
      | cons r4 tail =>
        cases tail with
        | cons r3 tail =>
          cases tail with
          | cons r2 tail =>
            cases tail with
            | cons r1 tail =>
              cases tail with
              | nil =>
                rename_i f5 f4 f3 f2 f1
                obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
                have successful : doApp (nextSource.refs, nextSource.ffi) .copyStrAw8 [v1,v2,v3,v4,v5] ≠ none := by
                  intro failed
                  apply safe nextSource
                  change EvaluateHOL.evaluate source sourceEnv [.app .copyStrAw8 [left, right, third, fourth, fifth]] = _
                  rw [EvaluateHOL.evaluate]
                  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                  rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [fifth, fourth, third, right, left] []).1, sourceRun]
                  simp [getOpClass, failed, EvaluateHOL.typeError]
                obtain ⟨text, offset, sliceLength, flag, address, dstOffset, bytes, rfl, rfl, rfl, rfl, rfl, lookup⟩ :=
                  copyStrAw8_operands nextSource v1 v2 v3 v4 v5 successful
                have f1Eq := (valueRel_literal_iff nextGenv (.strLit text) f1).mp r1
                have f2Eq := (valueRel_literal_iff nextGenv (.intLit offset) f2).mp r2
                have f3Eq := (valueRel_literal_iff nextGenv (.intLit sliceLength) f3).mp r3
                have f4Eq := (valueRel_location_iff nextGenv flag address f4).mp r4
                have f5Eq := (valueRel_literal_iff nextGenv (.intLit dstOffset) f5).mp r5
                subst f1; subst f2; subst f3; subst f4; subst f5
                have primitive := copyStrAw8_related nextGenv nextSource nextFlat states nextInvariant.1 text offset sliceLength flag address bytes dstOffset lookup
                cases sourceApp : doApp (nextSource.refs, nextSource.ffi) .copyStrAw8
                    [.litv (.strLit text), .litv (.intLit offset), .litv (.intLit sliceLength), .loc flag address, .litv (.intLit dstOffset)] with
                | none => exact (successful sourceApp).elim
                | some sourceOut =>
                  cases sourceOut with
                  | mk store sourceResult =>
                    cases store with
                    | mk refs ffi =>
                      cases flatApp : FlatSem.doAppCopy nextFlat .copyStrAw8
                          [.litv (.strLit text), .litv (.intLit offset), .litv (.intLit sliceLength), .loc flag (address+1), .litv (.intLit dstOffset)] with
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
                              rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [fifth, fourth, third, right, left] []).1, sourceRun]
                              simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                              rw [FlatSem.evaluate]
                              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                              rw [(FlatSem.fixClock_evaluations flatEnv flat
                                [compileExp trace compMap fifth, compileExp trace compMap fourth, compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
                                (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
                              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                                getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp,
                                FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, flatApp]
                              cases resultRel with
                              | value valueRel => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.value (.cons valueRel .nil)) stateRel
                              | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.raise valueRel) stateRel
                              | abort error => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.abort error) stateRel
                            · rw [EvaluateHOL.evaluate]
                              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                              rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [fifth, fourth, third, right, left] []).1, sourceRun]
                              simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                              rw [FlatSem.evaluate]
                              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                              rw [(FlatSem.fixClock_evaluations flatEnv flat
                                [compileExp trace compMap fifth, compileExp trace compMap fourth, compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
                                (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
                              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                                getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp,
                                FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, flatApp]
                              cases resultRel with
                              | value valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro finalInvariant' (And.intro nextGeneration forward))
                              | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro finalInvariant' (And.intro nextGeneration forward))
                              | abort error => simp [EvaluateHOL.listResult]

/-- Byte-array copy composes operand simulations in a local environment. -/
theorem localEnvBounded_copyAw8Aw8 {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (left right third fourth fifth : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right)
    (thirdIH : LocalEnvBoundedIH (F := F) interp transform limit third)
    (fourthIH : LocalEnvBoundedIH (F := F) interp transform limit fourth)
    (fifthIH : LocalEnvBoundedIH (F := F) interp transform limit fifth) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .copyAw8Aw8 [left, right, third, fourth, fifth]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [fifth, fourth, third, right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .copyAw8Aw8 [left, right, third, fourth, fifth]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [fifth, fourth, third, right, left] []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform limit [fifth, fourth, third, right, left]
    (by intro expr member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl | rfl | rfl <;> assumption)
    genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
  unfold ExprListSim at argsSim
  simp only [compileExps] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [fifth, fourth, third, right, left] = sourceResult at argsSim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap fifth, compileExp trace compMap fourth, compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left] = flatResult at argsSim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := argsSim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [fifth, fourth, third, right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap fifth, compileExp trace compMap fourth, compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [fifth, fourth, third, right, left] []).1, sourceRun]
      trivial
  | raise valueRel =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [fifth, fourth, third, right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap fifth, compileExp trace compMap fourth, compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.raise valueRel, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [fifth, fourth, third, right, left] []).1, sourceRun]
      simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
      rw [FlatSem.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap fifth, compileExp trace compMap fourth, compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact post
  | @value sourceValues flatValues valuesRel =>
    have length := EvaluateProps.evaluateLengthFull source nextSource sourceEnv [fifth, fourth, third, right, left] sourceValues sourceRun
    have five : ∃ v5 v4 v3 v2 v1, sourceValues = [v5, v4, v3, v2, v1] := by
      cases sourceValues with
      | nil => simp at length
      | cons v5 tail =>
        cases tail with
        | nil => simp at length
        | cons v4 tail =>
          cases tail with
          | nil => simp at length
          | cons v3 tail =>
            cases tail with
            | nil => simp at length
            | cons v2 tail =>
              cases tail with
              | nil => simp at length
              | cons v1 rest =>
                cases rest with
                | nil => exact ⟨v5, v4, v3, v2, v1, rfl⟩
                | cons extra rest => simp at length
    obtain ⟨v5, v4, v3, v2, v1, rfl⟩ := five
    cases valuesRel with
    | cons r5 tail =>
      cases tail with
      | cons r4 tail =>
        cases tail with
        | cons r3 tail =>
          cases tail with
          | cons r2 tail =>
            cases tail with
            | cons r1 tail =>
              cases tail with
              | nil =>
                rename_i f5 f4 f3 f2 f1
                obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
                have successful : doApp (nextSource.refs, nextSource.ffi) .copyAw8Aw8 [v1,v2,v3,v4,v5] ≠ none := by
                  intro failed
                  apply safe nextSource
                  change EvaluateHOL.evaluate source sourceEnv [.app .copyAw8Aw8 [left, right, third, fourth, fifth]] = _
                  rw [EvaluateHOL.evaluate]
                  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                  rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [fifth, fourth, third, right, left] []).1, sourceRun]
                  simp [getOpClass, failed, EvaluateHOL.typeError]
                obtain ⟨srcFlag, srcAddress, offset, sliceLength, flag, address, dstOffset, srcBytes, bytes, rfl, rfl, rfl, rfl, rfl, srcLookup, lookup⟩ :=
                  copyAw8Aw8_operands nextSource v1 v2 v3 v4 v5 successful
                have f1Eq := (valueRel_location_iff nextGenv srcFlag srcAddress f1).mp r1
                have f2Eq := (valueRel_literal_iff nextGenv (.intLit offset) f2).mp r2
                have f3Eq := (valueRel_literal_iff nextGenv (.intLit sliceLength) f3).mp r3
                have f4Eq := (valueRel_location_iff nextGenv flag address f4).mp r4
                have f5Eq := (valueRel_literal_iff nextGenv (.intLit dstOffset) f5).mp r5
                subst f1; subst f2; subst f3; subst f4; subst f5
                have primitive := copyAw8Aw8_related nextGenv nextSource nextFlat states nextInvariant.1 srcFlag srcAddress srcBytes offset sliceLength flag address bytes dstOffset srcLookup lookup
                cases sourceApp : doApp (nextSource.refs, nextSource.ffi) .copyAw8Aw8
                    [.loc srcFlag srcAddress, .litv (.intLit offset), .litv (.intLit sliceLength), .loc flag address, .litv (.intLit dstOffset)] with
                | none => exact (successful sourceApp).elim
                | some sourceOut =>
                  cases sourceOut with
                  | mk store sourceResult =>
                    cases store with
                    | mk refs ffi =>
                      cases flatApp : FlatSem.doAppCopy nextFlat .copyAw8Aw8
                          [.loc srcFlag (srcAddress + 1), .litv (.intLit offset), .litv (.intLit sliceLength), .loc flag (address+1), .litv (.intLit dstOffset)] with
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
                              rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [fifth, fourth, third, right, left] []).1, sourceRun]
                              simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                              rw [FlatSem.evaluate]
                              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                              rw [(FlatSem.fixClock_evaluations flatEnv flat
                                [compileExp trace compMap fifth, compileExp trace compMap fourth, compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
                                (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
                              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                                getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp,
                                FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, flatApp]
                              cases resultRel with
                              | value valueRel => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.value (.cons valueRel .nil)) stateRel
                              | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.raise valueRel) stateRel
                              | abort error => simpa [EvaluateHOL.listResult] using And.intro (ResultRel.abort error) stateRel
                            · rw [EvaluateHOL.evaluate]
                              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                              rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [fifth, fourth, third, right, left] []).1, sourceRun]
                              simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                              rw [FlatSem.evaluate]
                              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                              rw [(FlatSem.fixClock_evaluations flatEnv flat
                                [compileExp trace compMap fifth, compileExp trace compMap fourth, compileExp trace compMap third, compileExp trace compMap right, compileExp trace compMap left]
                                (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
                              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
                                getOpClass, astOpToFlatOp, sourceApp, FlatSem.applyResult, FlatSem.doApp,
                                FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, flatApp]
                              cases resultRel with
                              | value valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro finalInvariant' (And.intro nextGeneration forward))
                              | raise valueRel => simpa [EvaluateHOL.listResult] using And.intro growth (And.intro finalInvariant' (And.intro nextGeneration forward))
                              | abort error => simp [EvaluateHOL.listResult]

/-- External calls preserve related stores and the shared FFI state in arbitrary local environments. -/
theorem localEnvBounded_ffi {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (name : Basis.Pure.MlString.MlString) (left right : AstHOL.Exp)
    (leftIH : LocalEnvBoundedIH (F := F) interp transform limit left)
    (rightIH : LocalEnvBoundedIH (F := F) interp transform limit right) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app (.ffi name) [left, right]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [right, left] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app (.ffi name) [left, right]] = _
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
          have successful : doApp (nextSource.refs, nextSource.ffi) (.ffi name) [sourceSize, sourceValue] ≠ none := by
            intro failed
            apply safe nextSource
            change EvaluateHOL.evaluate source sourceEnv [.app (.ffi name) [left, right]] = _
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
            simp [getOpClass, failed, EvaluateHOL.typeError]
          obtain ⟨text, flag, address, bytes, rfl, rfl, lookup⟩ := ffi_operands nextSource name sourceSize sourceValue successful
          have flatText := (valueRel_literal_iff nextGenv (.strLit text) flatSize).mp sizeRel
          have flatPointer := (valueRel_location_iff nextGenv flag address flatValue).mp valueRel
          subst flatSize
          subst flatValue
          cases call : callFFIHOL nextSource.ffi (.extCall name) text.explode bytes with
          | final event =>
            obtain ⟨sourceApp, flatApp⟩ := ffi_final_related nextGenv nextSource nextFlat states name text flag address bytes event lookup call
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
                FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, flatApp]
              exact ⟨.abort _, states⟩
            · rw [EvaluateHOL.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
              rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
              simp [getOpClass, doApp, doAppNumericCore, sourceApp, EvaluateHOL.listResult]
          | ret nextFfi output =>
            obtain ⟨sourceRefs, flatRefs, sourceApp, flatApp, stateRel, reserved⟩ :=
              ffi_return_related nextGenv nextSource nextFlat states name text flag address bytes output nextFfi lookup call
            have finalInvariant := factoredInvariant_changeStoresFfi interp transform gen nextGenv (start, finish, other)
              nextSource nextFlat sourceRefs flatRefs nextFfi nextInvariant stateRel reserved
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
                FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, flatApp,
                FlatSem.unitValue, EvaluateHOL.listResult]
              exact ⟨.value (.cons (.tuple nextGenv [] [] (.nil nextGenv)) .nil), stateRel⟩
            · rw [EvaluateHOL.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
              rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [right, left] []).1, sourceRun]
              simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
              rw [FlatSem.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
              rw [(FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap right, compileExp trace compMap left]
                (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
              simpa [getOpClass, doApp, doAppNumericCore, sourceApp, astOpToFlatOp,
                FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, flatApp,
                FlatSem.unitValue, EvaluateHOL.listResult] using
                And.intro growth (And.intro finalInvariant (And.intro nextGeneration forward))


end Flapjack.Compiler.Backend.SourceToFlat
