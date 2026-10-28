import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalPrimitive

/-! Array primitive simulation in arbitrary related local environments.
These factored relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- A non-type-error dynamic allocation has an integer size operand. -/
theorem aalloc_size_operand {F : Type} (source : State F) (size value : Value)
    (successful : doApp (source.refs, source.ffi) .aalloc [size, value] ≠ none) :
    ∃ n, size = .litv (.intLit n) := by
  cases size <;> simp [doApp, doAppNumericCore, doAppBasic] at successful
  case litv lit =>
    cases lit <;> simp at successful
    case intLit n => exact ⟨n, rfl⟩

/-- A non-type-error byte-array allocation has integer size and Word8 value operands. -/
theorem aw8alloc_operands {F : Type} (source : State F) (size value : Value)
    (successful : doApp (source.refs, source.ffi) .aw8alloc [size, value] ≠ none) :
    ∃ n byte, size = .litv (.intLit n) ∧ value = .litv (.word8 byte) := by
  cases size <;> cases value <;> simp [doApp, doAppNumericCore, doAppBasic] at successful
  case litv.litv sizeLit valueLit =>
    cases sizeLit <;> cases valueLit <;> simp at successful
    case intLit.word8 n byte => exact ⟨n, byte, rfl, rfl⟩

/-- A successful array length operation identifies a source array cell. -/
theorem alength_operand {F : Type} (source : State F) (operand : Value)
    (successful : doApp (source.refs, source.ffi) .alength [operand] ≠ none) :
    ∃ flag address values, operand = .loc flag address ∧ storeLookup address source.refs = some (.varray values) := by
  cases operand <;> simp [doApp, doAppNumericCore, doAppBasic] at successful
  case loc flag address =>
    cases lookup : storeLookup address source.refs with
    | none => simp [lookup] at successful
    | some cell =>
      cases cell with
      | varray values => exact ⟨flag, address, values, rfl, lookup⟩
      | refv value => simp [lookup] at successful
      | w8array bytes => simp [lookup] at successful
      | thunk mode value => simp [lookup] at successful

/-- A successful byte-array length operation identifies a source byte-array cell. -/
theorem aw8length_operand {F : Type} (source : State F) (operand : Value)
    (successful : doApp (source.refs, source.ffi) .aw8length [operand] ≠ none) :
    ∃ flag address bytes, operand = .loc flag address ∧ storeLookup address source.refs = some (.w8array bytes) := by
  cases operand <;> simp [doApp, doAppNumericCore, doAppBasic] at successful
  case loc flag address =>
    cases lookup : storeLookup address source.refs with
    | none => simp [lookup] at successful
    | some cell =>
      cases cell with
      | w8array bytes => exact ⟨flag, address, bytes, rfl, lookup⟩
      | refv value => simp [lookup] at successful
      | varray values => simp [lookup] at successful
      | thunk mode value => simp [lookup] at successful

/-- A byte-array subscript without a type error has a location, integer
index, and byte-array store cell. -/
theorem aw8sub_operands {F : Type} (source : State F) (pointer index : Value) (unsafeOp : Bool)
    (successful : doApp (source.refs, source.ffi) (if unsafeOp then .aw8subUnsafe else .aw8sub)
      [pointer, index] ≠ none) :
    ∃ flag address n bytes, pointer = .loc flag address ∧ index = .litv (.intLit n) ∧
      storeLookup address source.refs = some (.w8array bytes) := by
  cases unsafeOp <;> cases pointer <;> cases index <;>
    simp [doApp, doAppNumericCore, doAppBasic] at successful
  all_goals rename_i flag address lit
  all_goals cases lit <;> simp at successful
  all_goals rename_i n
  all_goals cases lookup : storeLookup address source.refs <;> simp [lookup] at successful
  all_goals rename_i cell
  all_goals cases cell <;> simp at successful
  all_goals rename_i bytes
  all_goals exact ⟨flag, address, n, bytes, rfl, rfl, lookup⟩

/-- Byte-array subscript dispatch agrees on success, checked bounds errors,
and unchecked failure. Both states remain unchanged. -/
theorem aw8sub_complete_related {C F : Type} (genv : GlobalEnv)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (ok : genvCOk genv.c) (flag : Bool) (n : Nat)
    (bytes : List (BitVec 8)) (lookup : storeLookup n sourceState.refs = some (.w8array bytes))
    (index : Int) (unsafeOp : Bool) :
    let op := if unsafeOp then Flapjack.AstHOL.Op.aw8subUnsafe else .aw8sub
    match doApp (sourceState.refs, sourceState.ffi) op [.loc flag n, .litv (.intLit index)],
      FlatSem.doAppMemory flatState op [.loc flag (n + 1), .litv (.intLit index)] with
    | none, some none => True
    | some ((refs, ffi), result), some (some (nextFlat, flatResult)) =>
        refs = sourceState.refs ∧ ffi = sourceState.ffi ∧ nextFlat = flatState ∧ ResultRel ValueRel genv result flatResult
    | _, _ => False := by
  by_cases negative : index < 0
  · have ⟨src, dst, exceptionRel⟩ := aw8sub_outOfBounds genv sourceState flatState statesRel ok flag n bytes lookup
      index (Or.inl negative) unsafeOp
    cases unsafeOp <;> simp only [Bool.false_eq_true, if_false, if_true] at src dst ⊢ <;>
      simp [doApp, doAppNumericCore, src, dst, ResultRel.raise exceptionRel]
  · cases element : bytes[index.toNat]? with
    | none =>
      have ⟨src, dst, exceptionRel⟩ := aw8sub_outOfBounds genv sourceState flatState statesRel ok flag n bytes lookup
        index (Or.inr element) unsafeOp
      cases unsafeOp <;> simp only [Bool.false_eq_true, if_false, if_true] at src dst ⊢ <;>
        simp [doApp, doAppNumericCore, src, dst, ResultRel.raise exceptionRel]
    | some byte =>
      have ⟨src, dst, valueRel⟩ := aw8sub_related genv sourceState flatState statesRel flag n bytes lookup index
        (Int.le_of_not_gt negative) byte element unsafeOp
      cases unsafeOp <;> simp only [Bool.false_eq_true, if_false, if_true] at src dst ⊢ <;>
        simp [doApp, doAppNumericCore, src, dst, ResultRel.value valueRel]

/-- Fixed array allocation evaluates its fields right-to-left, restores the
source field order, and preserves the reserved flat store entry. -/
theorem localEnvIH_aallocFixed {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (args : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ args → LocalEnvIH (F := F) interp transform expr) :
    LocalEnvIH (F := F) interp transform (.app .aallocFixed args) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  change LocalExpressionStep interp transform genv start finish other source flat sourceEnv flatEnv trace compMap gen
    (.app .aallocFixed args)
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv args.reverse ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .aallocFixed args] = _
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := localEnvListStep_of_each interp transform args.reverse
    (fun expr member => each expr (List.mem_reverse.mp member)) genv start finish other source flat
    baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation argsSafe
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
theorem localEnvIH_aalloc {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvIH (F := F) interp transform left)
    (rightIH : LocalEnvIH (F := F) interp transform right) :
    LocalEnvIH (F := F) interp transform (.app .aalloc [left, right]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation safe
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
  obtain ⟨nextGenv, argsSim, post⟩ := localEnvListStep_of_each interp transform [right, left]
    (by intro expr member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl <;> assumption)
    genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation argsSafe
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
theorem localEnvIH_aw8alloc {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvIH (F := F) interp transform left)
    (rightIH : LocalEnvIH (F := F) interp transform right) :
    LocalEnvIH (F := F) interp transform (.app .aw8alloc [left, right]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation safe
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
  obtain ⟨nextGenv, argsSim, post⟩ := localEnvListStep_of_each interp transform [right, left]
    (by intro expr member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl <;> assumption)
    genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation argsSafe
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
theorem localEnvIH_alength {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (body : AstHOL.Exp)
    (bodyIH : LocalEnvIH (F := F) interp transform body) :
    LocalEnvIH (F := F) interp transform (.app .alength [body]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation safe
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
    trace baseMap gen localRel envInv tracesLen invariant generation bodySafe
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
theorem localEnvIH_aw8length {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (body : AstHOL.Exp)
    (bodyIH : LocalEnvIH (F := F) interp transform body) :
    LocalEnvIH (F := F) interp transform (.app .aw8length [body]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation safe
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
    trace baseMap gen localRel envInv tracesLen invariant generation bodySafe
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

/-- Covered expressions combine fixed array allocation with the previously covered forms. -/
inductive LocalEnvArrayExpression : AstHOL.Exp → Prop where
  | base (expr : AstHOL.Exp) : LocalEnvPrimitiveExpression expr → LocalEnvArrayExpression expr
  | arrayFixed (args : List AstHOL.Exp) : (∀ expr, expr ∈ args → LocalEnvArrayExpression expr) →
      LocalEnvArrayExpression (.app .aallocFixed args)
  | arrayAlloc (size value : AstHOL.Exp) : LocalEnvArrayExpression size → LocalEnvArrayExpression value →
      LocalEnvArrayExpression (.app .aalloc [size, value])
  | byteArrayAlloc (size value : AstHOL.Exp) : LocalEnvArrayExpression size → LocalEnvArrayExpression value →
      LocalEnvArrayExpression (.app .aw8alloc [size, value])
  | arrayLength (body : AstHOL.Exp) : LocalEnvArrayExpression body → LocalEnvArrayExpression (.app .alength [body])
  | byteArrayLength (body : AstHOL.Exp) : LocalEnvArrayExpression body → LocalEnvArrayExpression (.app .aw8length [body])
  | tuple (args : List AstHOL.Exp) : (∀ expr, expr ∈ args → LocalEnvArrayExpression expr) →
      LocalEnvArrayExpression (.con none args)
  | constructor (id : Ident ModN ConN) (args : List AstHOL.Exp) :
      (∀ expr, expr ∈ args → LocalEnvArrayExpression expr) → LocalEnvArrayExpression (.con (some id) args)
  | test (test : Test) (typ : PrimType) (left right : AstHOL.Exp) :
      LocalEnvArrayExpression left → LocalEnvArrayExpression right →
      LocalEnvArrayExpression (.app (.test test typ) [left, right])
  | equality (left right : AstHOL.Exp) : LocalEnvArrayExpression left → LocalEnvArrayExpression right →
      LocalEnvArrayExpression (.app .equality [left, right])
  | integerArith (action : Arith) (left right : AstHOL.Exp) :
      LocalEnvArrayExpression left → LocalEnvArrayExpression right →
      LocalEnvArrayExpression (.app (.arith action .intT) [left, right])
  | word8Arith (action : Arith) (left right : AstHOL.Exp) :
      LocalEnvArrayExpression left → LocalEnvArrayExpression right →
      LocalEnvArrayExpression (.app (.arith action (.wordT .w8)) [left, right])
  | word64Arith (action : Arith) (left right : AstHOL.Exp) :
      LocalEnvArrayExpression left → LocalEnvArrayExpression right →
      LocalEnvArrayExpression (.app (.arith action (.wordT .w64)) [left, right])
  | word8Shift (shift : Shift) (amount : Nat) (body : AstHOL.Exp) : LocalEnvArrayExpression body →
      LocalEnvArrayExpression (.app (.shift .w8 shift amount) [body])
  | word64Shift (shift : Shift) (amount : Nat) (body : AstHOL.Exp) : LocalEnvArrayExpression body →
      LocalEnvArrayExpression (.app (.shift .w64 shift amount) [body])
  | conversion (fromType toType : PrimType) (body : AstHOL.Exp) : LocalEnvArrayExpression body →
      LocalEnvArrayExpression (.app (.fromTo fromType toType) [body])
  | ref_ (body : AstHOL.Exp) : LocalEnvArrayExpression body →
      LocalEnvArrayExpression (.app .opref [body])
  | assign (left right : AstHOL.Exp) : LocalEnvArrayExpression left → LocalEnvArrayExpression right →
      LocalEnvArrayExpression (.app .opassign [left, right])
  | deref (body : AstHOL.Exp) : LocalEnvArrayExpression body →
      LocalEnvArrayExpression (.app .opderef [body])
  | letNamed (name : VarN) (first body : AstHOL.Exp) : LocalEnvArrayExpression first →
      LocalEnvArrayExpression body → LocalEnvArrayExpression (.let_ (some name) first body)
  | letAnonymous (first body : AstHOL.Exp) : LocalEnvArrayExpression first → LocalEnvArrayExpression body →
      LocalEnvArrayExpression (.let_ none first body)
  | if_ (cond yes no : AstHOL.Exp) : LocalEnvArrayExpression cond → LocalEnvArrayExpression yes →
      LocalEnvArrayExpression no → LocalEnvArrayExpression (.if_ cond yes no)
  | log (op : Lop) (left right : AstHOL.Exp) : LocalEnvArrayExpression left → LocalEnvArrayExpression right →
      LocalEnvArrayExpression (.log op left right)
  | raise_ (body : AstHOL.Exp) : LocalEnvArrayExpression body → LocalEnvArrayExpression (.raise body)
  | tannot (expr : AstHOL.Exp) (typ : AstT) : LocalEnvArrayExpression expr → LocalEnvArrayExpression (.tannot expr typ)
  | lannot (expr : AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs) : LocalEnvArrayExpression expr →
      LocalEnvArrayExpression (.lannot expr loc)

/-- Covered expressions satisfy the preliminary arbitrary-local hypothesis;
the relations remain pending HOL correspondence review. -/
theorem localEnvIH_arrayTree {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (expr : AstHOL.Exp) (covered : LocalEnvArrayExpression expr) : LocalEnvIH (F := F) interp transform expr := by
  induction covered with
  | base expr covered => exact localEnvIH_primitiveTree interp transform expr covered
  | arrayFixed args _ ih => exact localEnvIH_aallocFixed interp transform args ih
  | arrayAlloc size value _ _ sizeIH valueIH => exact localEnvIH_aalloc interp transform size value sizeIH valueIH
  | byteArrayAlloc size value _ _ sizeIH valueIH => exact localEnvIH_aw8alloc interp transform size value sizeIH valueIH
  | arrayLength body _ ih => exact localEnvIH_alength interp transform body ih
  | byteArrayLength body _ ih => exact localEnvIH_aw8length interp transform body ih
  | tuple args _ ih => exact localEnvIH_tuple interp transform args ih
  | constructor id args _ ih => exact localEnvIH_constructor interp transform id args ih
  | test test typ left right _ _ leftIH rightIH => exact localEnvIH_test interp transform test typ left right leftIH rightIH
  | equality left right _ _ leftIH rightIH => exact localEnvIH_equality interp transform left right leftIH rightIH
  | integerArith action left right _ _ leftIH rightIH =>
    exact localEnvIH_integerArith interp transform action left right leftIH rightIH
  | word8Arith action left right _ _ leftIH rightIH =>
    exact localEnvIH_word8Arith interp transform action left right leftIH rightIH
  | word64Arith action left right _ _ leftIH rightIH =>
    exact localEnvIH_word64Arith interp transform action left right leftIH rightIH
  | word8Shift shift amount body _ ih => exact localEnvIH_word8Shift interp transform body shift amount ih
  | word64Shift shift amount body _ ih => exact localEnvIH_word64Shift interp transform body shift amount ih
  | conversion fromType toType body _ ih =>
    exact localEnvIH_conversion interp transform body fromType toType ih
  | ref_ body _ ih => exact localEnvIH_opref interp transform body ih
  | assign left right _ _ leftIH rightIH => exact localEnvIH_opassign interp transform left right leftIH rightIH
  | deref body _ ih => exact localEnvIH_opderef interp transform body ih
  | letNamed name first body _ _ firstIH bodyIH => exact localEnvIH_let_named interp transform name first body firstIH bodyIH
  | letAnonymous first body _ _ firstIH bodyIH => exact localEnvIH_let_anonymous interp transform first body firstIH bodyIH
  | if_ cond yes no _ _ _ condIH yesIH noIH => exact localEnvIH_if interp transform cond yes no condIH yesIH noIH
  | log op left right _ _ leftIH rightIH => exact localEnvIH_log interp transform op left right leftIH rightIH
  | raise_ body _ ih => exact localEnvIH_raise interp transform body ih
  | tannot expr typ _ ih => exact localEnvIH_tannot interp transform expr typ ih
  | lannot expr loc _ ih => exact localEnvIH_lannot interp transform expr loc ih




end Flapjack.Compiler.Backend.SourceToFlat
