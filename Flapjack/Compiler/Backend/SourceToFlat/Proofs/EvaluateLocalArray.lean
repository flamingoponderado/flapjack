import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalPrimitive
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalMatch
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalCall
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalBoundedControl

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

/-- An array subscript without a type error has a location, integer
index, and array store cell. -/
theorem asub_operands {F : Type} (source : State F) (pointer index : Value) (unsafeOp : Bool)
    (successful : doApp (source.refs, source.ffi) (if unsafeOp then .asubUnsafe else .asub)
      [pointer, index] ≠ none) :
    ∃ flag address n values, pointer = .loc flag address ∧ index = .litv (.intLit n) ∧
      storeLookup address source.refs = some (.varray values) := by
  cases unsafeOp <;> cases pointer <;> cases index <;>
    simp [doApp, doAppNumericCore, doAppBasic] at successful
  all_goals rename_i flag address lit
  all_goals cases lit <;> simp at successful
  all_goals rename_i n
  all_goals cases lookup : storeLookup address source.refs <;> simp [lookup] at successful
  all_goals rename_i cell
  all_goals cases cell <;> simp at successful
  all_goals rename_i values
  all_goals exact ⟨flag, address, n, values, rfl, rfl, lookup⟩

/-- Array subscript dispatch preserves related results and states. -/
theorem asub_complete_related {C F : Type} (genv : GlobalEnv)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (ok : genvCOk genv.c) (flag : Bool) (n : Nat)
    (values : List SemanticPrimitivesHOL.Value) (lookup : storeLookup n sourceState.refs = some (.varray values))
    (index : Int) (unsafeOp : Bool) :
    let op := if unsafeOp then Flapjack.AstHOL.Op.asubUnsafe else .asub
    match doApp (sourceState.refs, sourceState.ffi) op [.loc flag n, .litv (.intLit index)],
      FlatSem.doAppMemory flatState op [.loc flag (n + 1), .litv (.intLit index)] with
    | none, some none => True
    | some ((refs, ffi), result), some (some (nextFlat, flatResult)) =>
        refs = sourceState.refs ∧ ffi = sourceState.ffi ∧ nextFlat = flatState ∧ ResultRel ValueRel genv result flatResult
    | _, _ => False := by
  by_cases negative : index < 0
  · have ⟨src, dst, exceptionRel⟩ := asub_outOfBounds genv sourceState flatState statesRel ok flag n values lookup
      index (Or.inl negative) unsafeOp
    cases unsafeOp <;> simp only [Bool.false_eq_true, if_false, if_true] at src dst ⊢ <;>
      simp [doApp, doAppNumericCore, src, dst, ResultRel.raise exceptionRel]
  · cases element : values[index.toNat]? with
    | none =>
      have ⟨src, dst, exceptionRel⟩ := asub_outOfBounds genv sourceState flatState statesRel ok flag n values lookup
        index (Or.inr element) unsafeOp
      cases unsafeOp <;> simp only [Bool.false_eq_true, if_false, if_true] at src dst ⊢ <;>
        simp [doApp, doAppNumericCore, src, dst, ResultRel.raise exceptionRel]
    | some value =>
      obtain ⟨flatValue, src, dst, valueRel⟩ := asub_related genv sourceState flatState statesRel flag n values lookup index
        (Int.le_of_not_gt negative) value element unsafeOp
      cases unsafeOp <;> simp only [Bool.false_eq_true, if_false, if_true] at src dst ⊢ <;>
        simp [doApp, doAppNumericCore, src, dst, ResultRel.value valueRel]

/-- A byte-array update without a type error has a byte-array location,
integer index, and byte value. -/
theorem aw8update_operands {F : Type} (source : State F) (pointer index value : Value) (unsafeOp : Bool)
    (successful : doApp (source.refs, source.ffi) (if unsafeOp then .aw8updateUnsafe else .aw8update)
      [pointer, index, value] ≠ none) :
    ∃ flag address n byte bytes, pointer = .loc flag address ∧ index = .litv (.intLit n) ∧
      value = .litv (.word8 byte) ∧ storeLookup address source.refs = some (.w8array bytes) := by
  cases unsafeOp <;> cases pointer <;> cases index <;> cases value <;>
    simp [doApp, doAppNumericCore, doAppBasic] at successful
  all_goals rename_i flag address indexLit valueLit
  all_goals cases indexLit <;> cases valueLit <;> simp at successful
  all_goals rename_i n byte
  all_goals cases lookup : storeLookup address source.refs <;> simp [lookup] at successful
  all_goals rename_i cell
  all_goals cases cell <;> simp at successful
  all_goals rename_i bytes
  all_goals exact ⟨flag, address, n, byte, bytes, rfl, rfl, rfl, lookup⟩

/-- Checked and unchecked byte-array updates preserve the factored state
relation, result relation, and reserved flat store entry. -/
theorem aw8update_complete_related {C F : Type} (genv : GlobalEnv)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (ok : genvCOk genv.c) (flag : Bool) (n : Nat)
    (bytes : List (BitVec 8)) (lookup : storeLookup n sourceState.refs = some (.w8array bytes))
    (index : Int) (byte : BitVec 8) (unsafeOp : Bool) :
    let op := if unsafeOp then Flapjack.AstHOL.Op.aw8updateUnsafe else .aw8update
    match doApp (sourceState.refs, sourceState.ffi) op [.loc flag n, .litv (.intLit index), .litv (.word8 byte)],
      FlatSem.doAppMemory flatState op [.loc flag (n + 1), .litv (.intLit index), .litv (.word8 byte)] with
    | none, some none => True
    | some ((refs, ffi), result), some (some (nextFlat, flatResult)) =>
        ffi = sourceState.ffi ∧ nextFlat = { flatState with refs := nextFlat.refs } ∧
        StateRel genv { sourceState with refs := refs } nextFlat ∧
        nextFlat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv result flatResult
    | _, _ => False := by
  by_cases negative : index < 0
  · have ⟨src, dst, exceptionRel⟩ := aw8update_outOfBounds genv sourceState flatState statesRel ok flag n bytes lookup
      index (Or.inl negative) byte unsafeOp
    cases unsafeOp <;> simp only [Bool.false_eq_true, if_false, if_true] at src dst ⊢ <;>
      simp [doApp, doAppNumericCore, src, dst, statesRel, ResultRel.raise exceptionRel]
  · by_cases inBounds : index.toNat < bytes.length
    · obtain ⟨flatRefs, src, dst, valueRel, nextRel, reserved⟩ := aw8update_related genv sourceState flatState
        statesRel flag n bytes lookup index (Int.le_of_not_gt negative) inBounds byte unsafeOp
      cases unsafeOp <;> simp only [Bool.false_eq_true, if_false, if_true] at src dst ⊢ <;>
        simp [doApp, doAppNumericCore, src, dst, nextRel, reserved, ResultRel.value valueRel]
    · have ⟨src, dst, exceptionRel⟩ := aw8update_outOfBounds genv sourceState flatState statesRel ok flag n bytes lookup
        index (Or.inr (Nat.le_of_not_gt inBounds)) byte unsafeOp
      cases unsafeOp <;> simp only [Bool.false_eq_true, if_false, if_true] at src dst ⊢ <;>
        simp [doApp, doAppNumericCore, src, dst, statesRel, ResultRel.raise exceptionRel]

/-- A value-array update without a type error has an array location and integer index. -/
theorem aupdate_operands {F : Type} (source : State F) (pointer index value : Value) (unsafeOp : Bool)
    (successful : doApp (source.refs, source.ffi) (if unsafeOp then .aupdateUnsafe else .aupdate)
      [pointer, index, value] ≠ none) :
    ∃ flag address n values, pointer = .loc flag address ∧ index = .litv (.intLit n) ∧
      storeLookup address source.refs = some (.varray values) := by
  cases unsafeOp <;> cases pointer <;> cases index <;>
    simp [doApp, doAppNumericCore, doAppBasic] at successful
  all_goals rename_i flag address indexLit
  all_goals cases indexLit <;> simp at successful
  all_goals rename_i n
  all_goals cases lookup : storeLookup address source.refs <;> simp [lookup] at successful
  all_goals rename_i cell
  all_goals cases cell <;> simp at successful
  all_goals rename_i values
  all_goals exact ⟨flag, address, n, values, rfl, rfl, lookup⟩

/-- Checked and unchecked value-array updates preserve the factored state
relation, result relation, and reserved flat store entry. -/
theorem aupdate_complete_related {C F : Type} (genv : GlobalEnv)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (ok : genvCOk genv.c) (flag : Bool) (n : Nat)
    (values : List SemanticPrimitivesHOL.Value) (lookup : storeLookup n sourceState.refs = some (.varray values))
    (index : Int) (value : SemanticPrimitivesHOL.Value) (flatValue : FlatSem.Value)
    (valueRel : ValueRel genv value flatValue) (unsafeOp : Bool) :
    let op := if unsafeOp then Flapjack.AstHOL.Op.aupdateUnsafe else .aupdate
    match doApp (sourceState.refs, sourceState.ffi) op [.loc flag n, .litv (.intLit index), value],
      FlatSem.doAppMemory flatState op [.loc flag (n + 1), .litv (.intLit index), flatValue] with
    | none, some none => True
    | some ((refs, ffi), result), some (some (nextFlat, flatResult)) =>
        ffi = sourceState.ffi ∧ nextFlat = { flatState with refs := nextFlat.refs } ∧
        StateRel genv { sourceState with refs := refs } nextFlat ∧
        nextFlat.refs.take 1 = flatState.refs.take 1 ∧ ResultRel ValueRel genv result flatResult
    | _, _ => False := by
  by_cases negative : index < 0
  · have ⟨src, dst, exceptionRel⟩ := aupdate_outOfBounds genv sourceState flatState statesRel ok flag n values lookup
      index (Or.inl negative) value flatValue unsafeOp
    cases unsafeOp <;> simp only [Bool.false_eq_true, if_false, if_true] at src dst ⊢ <;>
      simp [doApp, doAppNumericCore, src, dst, statesRel, ResultRel.raise exceptionRel]
  · by_cases inBounds : index.toNat < values.length
    · obtain ⟨flatRefs, src, dst, resultRel, nextRel, reserved⟩ := aupdate_related genv sourceState flatState
        statesRel flag n values lookup index (Int.le_of_not_gt negative) inBounds value flatValue valueRel unsafeOp
      cases unsafeOp <;> simp only [Bool.false_eq_true, if_false, if_true] at src dst ⊢ <;>
        simp [doApp, doAppNumericCore, src, dst, nextRel, reserved, ResultRel.value resultRel]
    · have ⟨src, dst, exceptionRel⟩ := aupdate_outOfBounds genv sourceState flatState statesRel ok flag n values lookup
        index (Or.inr (Nat.le_of_not_gt inBounds)) value flatValue unsafeOp
      cases unsafeOp <;> simp only [Bool.false_eq_true, if_false, if_true] at src dst ⊢ <;>
        simp [doApp, doAppNumericCore, src, dst, statesRel, ResultRel.raise exceptionRel]

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

/-- Compose aw8sub operand hypotheses in an arbitrary local environment. -/
theorem localEnvIH_aw8sub {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvIH (F := F) interp transform left)
    (rightIH : LocalEnvIH (F := F) interp transform right) :
    LocalEnvIH (F := F) interp transform (.app .aw8sub [left, right]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation safe
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
theorem localEnvIH_aw8subUnsafe {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvIH (F := F) interp transform left)
    (rightIH : LocalEnvIH (F := F) interp transform right) :
    LocalEnvIH (F := F) interp transform (.app .aw8subUnsafe [left, right]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation safe
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
theorem localEnvIH_asub {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvIH (F := F) interp transform left)
    (rightIH : LocalEnvIH (F := F) interp transform right) :
    LocalEnvIH (F := F) interp transform (.app .asub [left, right]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation safe
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
theorem localEnvIH_asubUnsafe {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (left right : AstHOL.Exp)
    (leftIH : LocalEnvIH (F := F) interp transform left)
    (rightIH : LocalEnvIH (F := F) interp transform right) :
    LocalEnvIH (F := F) interp transform (.app .asubUnsafe [left, right]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation safe
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
theorem localEnvIH_aupdate {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (left right third : AstHOL.Exp)
    (leftIH : LocalEnvIH (F := F) interp transform left)
    (rightIH : LocalEnvIH (F := F) interp transform right)
    (thirdIH : LocalEnvIH (F := F) interp transform third) :
    LocalEnvIH (F := F) interp transform (.app .aupdate [left, right, third]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation safe
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
  obtain ⟨nextGenv, argsSim, post⟩ := localEnvListStep_of_each interp transform [third, right, left]
    (by intro expr member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl <;> assumption)
    genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation argsSafe
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
theorem localEnvIH_aupdateUnsafe {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (left right third : AstHOL.Exp)
    (leftIH : LocalEnvIH (F := F) interp transform left)
    (rightIH : LocalEnvIH (F := F) interp transform right)
    (thirdIH : LocalEnvIH (F := F) interp transform third) :
    LocalEnvIH (F := F) interp transform (.app .aupdateUnsafe [left, right, third]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation safe
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
  obtain ⟨nextGenv, argsSim, post⟩ := localEnvListStep_of_each interp transform [third, right, left]
    (by intro expr member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl <;> assumption)
    genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation argsSafe
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
theorem localEnvIH_aw8update {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (left right third : AstHOL.Exp)
    (leftIH : LocalEnvIH (F := F) interp transform left)
    (rightIH : LocalEnvIH (F := F) interp transform right)
    (thirdIH : LocalEnvIH (F := F) interp transform third) :
    LocalEnvIH (F := F) interp transform (.app .aw8update [left, right, third]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation safe
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
  obtain ⟨nextGenv, argsSim, post⟩ := localEnvListStep_of_each interp transform [third, right, left]
    (by intro expr member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl <;> assumption)
    genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation argsSafe
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
theorem localEnvIH_aw8updateUnsafe {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (left right third : AstHOL.Exp)
    (leftIH : LocalEnvIH (F := F) interp transform left)
    (rightIH : LocalEnvIH (F := F) interp transform right)
    (thirdIH : LocalEnvIH (F := F) interp transform third) :
    LocalEnvIH (F := F) interp transform (.app .aw8updateUnsafe [left, right, third]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation safe
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
  obtain ⟨nextGenv, argsSim, post⟩ := localEnvListStep_of_each interp transform [third, right, left]
    (by intro expr member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl <;> assumption)
    genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen localRel envInv tracesLen invariant generation argsSafe
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

/-- Covered expressions combine fixed array allocation with the previously covered forms. -/
inductive LocalEnvArrayExpression : AstHOL.Exp → Prop where
  | base (expr : AstHOL.Exp) : LocalEnvPrimitiveExpression expr → LocalEnvArrayExpression expr
  | arrayFixed (args : List AstHOL.Exp) : (∀ expr, expr ∈ args → LocalEnvArrayExpression expr) →
      LocalEnvArrayExpression (.app .aallocFixed args)
  | arrayAlloc (size value : AstHOL.Exp) : LocalEnvArrayExpression size → LocalEnvArrayExpression value →
      LocalEnvArrayExpression (.app .aalloc [size, value])
  | byteArrayAlloc (size value : AstHOL.Exp) : LocalEnvArrayExpression size → LocalEnvArrayExpression value →
      LocalEnvArrayExpression (.app .aw8alloc [size, value])
  | arrayUpdate (pointer index value : AstHOL.Exp) : LocalEnvArrayExpression pointer → LocalEnvArrayExpression index →
      LocalEnvArrayExpression value → LocalEnvArrayExpression (.app .aupdate [pointer, index, value])
  | arrayUpdateUnsafe (pointer index value : AstHOL.Exp) : LocalEnvArrayExpression pointer → LocalEnvArrayExpression index →
      LocalEnvArrayExpression value → LocalEnvArrayExpression (.app .aupdateUnsafe [pointer, index, value])
  | byteUpdate (pointer index value : AstHOL.Exp) : LocalEnvArrayExpression pointer → LocalEnvArrayExpression index →
      LocalEnvArrayExpression value → LocalEnvArrayExpression (.app .aw8update [pointer, index, value])
  | byteUpdateUnsafe (pointer index value : AstHOL.Exp) : LocalEnvArrayExpression pointer → LocalEnvArrayExpression index →
      LocalEnvArrayExpression value → LocalEnvArrayExpression (.app .aw8updateUnsafe [pointer, index, value])
  | arraySubscript (pointer index : AstHOL.Exp) : LocalEnvArrayExpression pointer → LocalEnvArrayExpression index →
      LocalEnvArrayExpression (.app .asub [pointer, index])
  | arraySubscriptUnsafe (pointer index : AstHOL.Exp) : LocalEnvArrayExpression pointer → LocalEnvArrayExpression index →
      LocalEnvArrayExpression (.app .asubUnsafe [pointer, index])
  | byteSubscript (pointer index : AstHOL.Exp) : LocalEnvArrayExpression pointer → LocalEnvArrayExpression index →
      LocalEnvArrayExpression (.app .aw8sub [pointer, index])
  | byteSubscriptUnsafe (pointer index : AstHOL.Exp) : LocalEnvArrayExpression pointer → LocalEnvArrayExpression index →
      LocalEnvArrayExpression (.app .aw8subUnsafe [pointer, index])
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
  | mat (body : AstHOL.Exp) (rows : List (Pat × AstHOL.Exp)) : LocalEnvArrayExpression body →
      (∀ pattern rowBody, (pattern, rowBody) ∈ rows → LocalEnvArrayExpression rowBody) →
      LocalEnvArrayExpression (.mat body rows)
  | handle (body : AstHOL.Exp) (rows : List (Pat × AstHOL.Exp)) : LocalEnvArrayExpression body →
      (∀ pattern rowBody, (pattern, rowBody) ∈ rows → LocalEnvArrayExpression rowBody) →
      LocalEnvArrayExpression (.handle body rows)
  | letrec (funs : List (VarN × VarN × AstHOL.Exp)) (body : AstHOL.Exp) :
      LocalEnvArrayExpression body → LocalEnvArrayExpression (.letrec funs body)
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
  | arrayUpdate pointer index value _ _ _ pointerIH indexIH valueIH =>
    exact localEnvIH_aupdate interp transform pointer index value pointerIH indexIH valueIH
  | arrayUpdateUnsafe pointer index value _ _ _ pointerIH indexIH valueIH =>
    exact localEnvIH_aupdateUnsafe interp transform pointer index value pointerIH indexIH valueIH
  | byteUpdate pointer index value _ _ _ pointerIH indexIH valueIH =>
    exact localEnvIH_aw8update interp transform pointer index value pointerIH indexIH valueIH
  | byteUpdateUnsafe pointer index value _ _ _ pointerIH indexIH valueIH =>
    exact localEnvIH_aw8updateUnsafe interp transform pointer index value pointerIH indexIH valueIH
  | arraySubscript pointer index _ _ pointerIH indexIH =>
    exact localEnvIH_asub interp transform pointer index pointerIH indexIH
  | arraySubscriptUnsafe pointer index _ _ pointerIH indexIH =>
    exact localEnvIH_asubUnsafe interp transform pointer index pointerIH indexIH
  | byteSubscript pointer index _ _ pointerIH indexIH =>
    exact localEnvIH_aw8sub interp transform pointer index pointerIH indexIH
  | byteSubscriptUnsafe pointer index _ _ pointerIH indexIH =>
    exact localEnvIH_aw8subUnsafe interp transform pointer index pointerIH indexIH
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
  | mat body rows _ _ bodyIH rowsIH => exact localEnvIH_mat interp transform body rows bodyIH rowsIH
  | handle body rows _ _ bodyIH rowsIH => exact localEnvIH_handle interp transform body rows bodyIH rowsIH
  | letrec funs body _ ih => exact localEnvIH_letrec interp transform funs body ih
  | letNamed name first body _ _ firstIH bodyIH => exact localEnvIH_let_named interp transform name first body firstIH bodyIH
  | letAnonymous first body _ _ firstIH bodyIH => exact localEnvIH_let_anonymous interp transform first body firstIH bodyIH
  | if_ cond yes no _ _ _ condIH yesIH noIH => exact localEnvIH_if interp transform cond yes no condIH yesIH noIH
  | log op left right _ _ leftIH rightIH => exact localEnvIH_log interp transform op left right leftIH rightIH
  | raise_ body _ ih => exact localEnvIH_raise interp transform body ih
  | tannot expr typ _ ih => exact localEnvIH_tannot interp transform expr typ ih
  | lannot expr loc _ ih => exact localEnvIH_lannot interp transform expr loc ih




end Flapjack.Compiler.Backend.SourceToFlat
