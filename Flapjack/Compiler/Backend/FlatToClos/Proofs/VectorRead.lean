import Flapjack.Compiler.Backend.FlatToClos.Proofs.ArrayRead

/-! Vector indexing prerequisites for flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- The emitted checked vector read returns the indexed closure value. -/
theorem evaluate_checkedVectorRead_inBounds {C F : Type} (state : ClosSem.State C F)
    (trace : BackendCommon.Tra) (env : List ClosSem.Value)
    (items : List ClosSem.Value) (index : Int) (value : ClosSem.Value)
    (nonnegative : ¬index < 0) (element : items[index.toNat]? = some value) :
    ClosSem.evaluate
      [.ifThenElse trace
        (.op trace (.blockOp .boundsCheckBlock) [.var trace 0, .var trace 1])
        (.op trace (.memOp .el) [.var trace 0, .var trace 1])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))]
      (.number index :: .block 0 items :: env) state = (.val [value], state) := by
  have bound : index.toNat < items.length := (List.getElem?_eq_some_iff.mp element).1
  have valueEq : items[index.toNat] = value := (List.getElem?_eq_some_iff.mp element).2
  have valid : 0 ≤ index ∧ index < (items.length : Int) := by omega
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyMemory, ClosSem.applyBlock,
    ClosSem.boolValue, ClosSem.asBool, BackendCommon.trueTag, valid, nonnegative, valueEq]

/-- The emitted checked vector read raises Subscript outside bounds. -/
theorem evaluate_checkedVectorRead_outOfBounds {C F : Type} (state : ClosSem.State C F)
    (trace : BackendCommon.Tra) (env : List ClosSem.Value) (items : List ClosSem.Value) (index : Int)
    (bad : index < 0 ∨ items.length ≤ index.toNat) :
    ClosSem.evaluate
      [.ifThenElse trace
        (.op trace (.blockOp .boundsCheckBlock) [.var trace 0, .var trace 1])
        (.op trace (.memOp .el) [.var trace 0, .var trace 1])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))]
      (.number index :: .block 0 items :: env) state = (.err (.raise (.block 3 [])), state) := by
  have invalid : ¬(0 ≤ index ∧ index < (items.length : Int)) := by omega
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
    ClosSem.boolValue, ClosSem.asBool, BackendCommon.falseTag, invalid]

/-- The checked vector read body preserves states and returns related values
or the related Subscript exception. -/
theorem checkedVectorRead_body_related {C F : Type} (source : FlatSem.State C F)
    (target : ClosSem.State C F) (trace : BackendCommon.Tra) (env : List ClosSem.Value)
    (items : List FlatSem.Value) (targetItems : List ClosSem.Value) (index : Int)
    (states : StateRel source target) (related : List.Forall₂ ValueRel items targetItems) :
    let flat := FlatSem.applyResult source (.src .vsub) [.vectorv items, .litv (.intLit index)]
    let clos := ClosSem.evaluate
      [.ifThenElse trace
        (.op trace (.blockOp .boundsCheckBlock) [.var trace 0, .var trace 1])
        (.op trace (.memOp .el) [.var trace 0, .var trace 1])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))]
      (.number index :: .block 0 targetItems :: env) target
    StateRel flat.1 clos.2 ∧ EvalResultRel flat.2 clos.1 := by
  have sameLength := related.length_eq
  have exception : ValueRel FlatSem.subscriptExnV (.block 3 []) := .con .nil
  by_cases negative : index < 0
  · have body := evaluate_checkedVectorRead_outOfBounds target trace env targetItems index (Or.inl negative)
    simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData,
      FlatSem.readIndexed, FlatSem.boundsFailure, negative, body, states, EvalResultRel.raise exception]
  · cases element : items[index.toNat]? with
    | none =>
      have bound : targetItems.length ≤ index.toNat := by
        have bound := List.getElem?_eq_none_iff.mp element
        omega
      have body := evaluate_checkedVectorRead_outOfBounds target trace env targetItems index (Or.inr bound)
      simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData,
        FlatSem.readIndexed, FlatSem.boundsFailure, negative, element, body, states, EvalResultRel.raise exception]
    | some value =>
      obtain ⟨targetValue, targetElement, valueRel⟩ := valueList_get_related items targetItems index.toNat value related element
      have body := evaluate_checkedVectorRead_inBounds target trace env targetItems index targetValue negative targetElement
      simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData,
        FlatSem.readIndexed, negative, element, body, states, EvalResultRel.value (.cons valueRel .nil)]


/-- Checked vector reads reject any argument count other than two. -/
theorem checkedVectorRead_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 2) :
    (FlatSem.applyResult state (.src .vsub) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData]
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData]
    | cons second rest =>
      cases rest with
      | nil => simp at wrong
      | cons third rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData]

/-- Checked vector indexing simulates the source expression for arbitrary
argument lists whenever the source does not report a type error. -/
theorem evaluate_checkedVectorRead {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src .vsub) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src .vsub) args] := by
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have closFix := ClosSem.fixClock_evaluate (compileExps names args).reverse values target
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate]
    simp only [flatFix, failure]
  have argsSim := argsSim argsNotTypeError
  unfold EvalSim at argsSim ⊢
  simp only [compile, compileExps, compileExp, compileOp] at ⊢
  simp only [compile, compileExps_reverse] at argsSim
  rw [FlatSem.evaluate, ClosSem.evaluate, closFix]
  simp only [flatFix]
  cases flatRun : FlatSem.evaluate env source args.reverse with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate (compileExps names args).reverse values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at argsSim ⊢
      rcases argsSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        rename_i sourceArgs targetArgs
        have resultShape : (FlatSem.applyResult next (.src .vsub) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 2 := by
          by_contra wrong
          apply resultShape
          apply checkedVectorRead_wrong_arity
          simpa using wrong
        cases related with
        | nil => simp at length
        | cons indexRel tail =>
          cases tail with
          | nil => simp at length
          | cons pointerRel tail =>
            cases tail with
            | cons _ _ => simp at length
            | nil =>
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at resultShape
              cases indexRel <;> cases pointerRel <;>
                simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
                  FlatSem.doAppMemory, FlatSem.doAppData] at resultShape
              case int.vector index sourceItems targetItems itemRel =>
                simpa using checkedVectorRead_body_related next nextTarget trace values sourceItems targetItems index states itemRel


/-- Unchecked vector reads reject any argument count other than two. -/
theorem uncheckedVectorRead_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 2) :
    (FlatSem.applyResult state (.src .vsubUnsafe) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData]
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData]
    | cons second rest =>
      cases rest with
      | nil => simp at wrong
      | cons third rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData]

/-- Unchecked vector indexing simulates the source expression for arbitrary
argument lists whenever the source does not report a type error. -/
theorem evaluate_uncheckedVectorRead {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src .vsubUnsafe) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src .vsubUnsafe) args] := by
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have closFix := ClosSem.fixClock_evaluate (compileExps names args).reverse values target
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate]
    simp only [flatFix, failure]
  have argsSim := argsSim argsNotTypeError
  unfold EvalSim at argsSim ⊢
  simp only [compile, compileExps, compileExp, compileOp] at ⊢
  simp only [compile, compileExps_reverse] at argsSim
  rw [FlatSem.evaluate, ClosSem.evaluate, closFix]
  simp only [flatFix]
  cases flatRun : FlatSem.evaluate env source args.reverse with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate (compileExps names args).reverse values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at argsSim ⊢
      rcases argsSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        rename_i sourceArgs targetArgs
        have resultShape : (FlatSem.applyResult next (.src .vsubUnsafe) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 2 := by
          by_contra wrong
          apply resultShape
          apply uncheckedVectorRead_wrong_arity
          simpa using wrong
        cases related with
        | nil => simp at length
        | cons indexRel tail =>
          cases tail with
          | nil => simp at length
          | cons pointerRel tail =>
            cases tail with
            | cons _ _ => simp at length
            | nil =>
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at resultShape
              cases indexRel <;> cases pointerRel <;>
                simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
                  FlatSem.doAppMemory, FlatSem.doAppData] at resultShape
              case int.vector index sourceItems targetItems itemRel =>
                by_cases negative : index < 0
                · simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative] at resultShape
                · cases element : sourceItems[index.toNat]? with
                  | none => simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative, element] at resultShape
                  | some value =>
                    obtain ⟨targetValue, targetElement, valueRel⟩ :=
                      valueList_get_related sourceItems targetItems index.toNat value itemRel element
                    simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                      FlatSem.doAppData, FlatSem.readIndexed, negative, element, ClosSem.doApp,
                      ClosSem.applyMemory, targetElement, states, EvalResultRel.value (.cons valueRel .nil)]


/-- Vector length rejects any argument count other than one. -/
theorem vectorLength_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 1) :
    (FlatSem.applyResult state (.src .vlength) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData]
  | cons first rest =>
    cases rest with
    | nil => simp at wrong
    | cons second rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData]

/-- Related vectors have the same length after evaluating arbitrary
argument lists, provided the source application avoids a type error. -/
theorem evaluate_vectorLength {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src .vlength) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src .vlength) args] := by
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have closFix := ClosSem.fixClock_evaluate (compileExps names args).reverse values target
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate]
    simp only [flatFix, failure]
  have argSim := argSim argsNotTypeError
  unfold EvalSim at argSim ⊢
  simp only [compile, compileExps_reverse] at argSim
  simp only [compile, compileExps, compileExp, compileOp] at ⊢
  rw [FlatSem.evaluate, ClosSem.evaluate, closFix]
  simp only [flatFix]
  cases flatRun : FlatSem.evaluate env source args.reverse with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate (compileExps names args).reverse values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at argSim ⊢
      rcases argSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        rename_i sourceArgs targetArgs
        have resultShape : (FlatSem.applyResult next (.src .vlength) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 1 := by
          by_contra wrong
          apply resultShape
          apply vectorLength_wrong_arity
          simpa using wrong
        cases related with
        | nil => simp at length
        | cons head tail =>
          cases tail with
          | cons _ _ => simp at length
          | nil =>
            simp only [List.reverse_singleton] at resultShape
            cases head <;> simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
              FlatSem.doAppMemory, FlatSem.doAppData] at resultShape
            case vector items targetItems itemRel =>
              have sameLength := itemRel.length_eq
              simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                FlatSem.doAppData, ClosSem.doApp, ClosSem.applyBlock, ← sameLength, states,
                EvalResultRel.value (.cons (ValueRel.int _) .nil)]


/-- String length rejects any argument count other than one. -/
theorem stringLength_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 1) :
    (FlatSem.applyResult state (.src .strlen) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData]
  | cons first rest =>
    cases rest with
    | nil => simp at wrong
    | cons second rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData]

/-- Related strings have the same byte length after evaluating arbitrary
argument lists, provided the source application avoids a type error. -/
theorem evaluate_stringLength {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src .strlen) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src .strlen) args] := by
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have closFix := ClosSem.fixClock_evaluate (compileExps names args).reverse values target
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate]
    simp only [flatFix, failure]
  have argSim := argSim argsNotTypeError
  unfold EvalSim at argSim ⊢
  simp only [compile, compileExps_reverse] at argSim
  simp only [compile, compileExps, compileExp, compileOp] at ⊢
  rw [FlatSem.evaluate, ClosSem.evaluate, closFix]
  simp only [flatFix]
  cases flatRun : FlatSem.evaluate env source args.reverse with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate (compileExps names args).reverse values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at argSim ⊢
      rcases argSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        rename_i sourceArgs targetArgs
        have resultShape : (FlatSem.applyResult next (.src .strlen) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 1 := by
          by_contra wrong
          apply resultShape
          apply stringLength_wrong_arity
          simpa using wrong
        cases related with
        | nil => simp at length
        | cons head tail =>
          cases tail with
          | cons _ _ => simp at length
          | nil =>
            simp only [List.reverse_singleton] at resultShape
            cases head <;> simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
              FlatSem.doAppMemory, FlatSem.doAppData] at resultShape
            case string str =>
              simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                FlatSem.doAppData, ClosSem.doApp, ClosSem.applyMemory, states,
                EvalResultRel.value (.cons (ValueRel.int _) .nil)]

/-- The emitted checked string read returns the selected byte as a number. -/
theorem evaluate_checkedStringRead_inBounds {C F : Type} (state : ClosSem.State C F)
    (trace : BackendCommon.Tra) (env : List ClosSem.Value)
    (bytes : List (BitVec 8)) (index : Int) (byte : BitVec 8)
    (nonnegative : ¬index < 0) (element : bytes[index.toNat]? = some byte) :
    ClosSem.evaluate
      [.ifThenElse trace
        (.op trace (.memOp (.boundsCheckByte false)) [.var trace 0, .var trace 1])
        (.op trace (.memOp .derefByteVec) [.var trace 0, .var trace 1])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))]
      (.number index :: .byteVector bytes :: env) state = (.val [.number byte.toNat], state) := by
  have bound : index.toNat < bytes.length := (List.getElem?_eq_some_iff.mp element).1
  have byteEq : bytes[index.toNat] = byte := (List.getElem?_eq_some_iff.mp element).2
  have valid : 0 ≤ index ∧ index < (bytes.length : Int) := by omega
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyMemory,
    ClosSem.boolValue, ClosSem.asBool, BackendCommon.trueTag, valid, nonnegative, byteEq]

/-- The emitted checked string read raises Subscript outside bounds. -/
theorem evaluate_checkedStringRead_outOfBounds {C F : Type} (state : ClosSem.State C F)
    (trace : BackendCommon.Tra) (env : List ClosSem.Value) (bytes : List (BitVec 8)) (index : Int)
    (bad : index < 0 ∨ bytes.length ≤ index.toNat) :
    ClosSem.evaluate
      [.ifThenElse trace
        (.op trace (.memOp (.boundsCheckByte false)) [.var trace 0, .var trace 1])
        (.op trace (.memOp .derefByteVec) [.var trace 0, .var trace 1])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))]
      (.number index :: .byteVector bytes :: env) state = (.err (.raise (.block 3 [])), state) := by
  have invalid : ¬(0 ≤ index ∧ index < (bytes.length : Int)) := by omega
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyMemory, ClosSem.applyBlock,
    ClosSem.boolValue, ClosSem.asBool, BackendCommon.falseTag, invalid]

/-- The emitted checked string read preserves states and returns a related
character or the related Subscript exception. -/
theorem checkedStringRead_body_related {C F : Type} (source : FlatSem.State C F)
    (target : ClosSem.State C F) (trace : BackendCommon.Tra) (env : List ClosSem.Value)
    (str : MlString) (index : Int) (states : StateRel source target) :
    let flat := FlatSem.applyResult source (.src .strsub) [.litv (.strLit str), .litv (.intLit index)]
    let clos := ClosSem.evaluate
      [.ifThenElse trace
        (.op trace (.memOp (.boundsCheckByte false)) [.var trace 0, .var trace 1])
        (.op trace (.memOp .derefByteVec) [.var trace 0, .var trace 1])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))]
      (.number index :: .byteVector str.explode :: env) target
    StateRel flat.1 clos.2 ∧ EvalResultRel flat.2 clos.1 := by
  have exception : ValueRel FlatSem.subscriptExnV (.block 3 []) := .con .nil
  by_cases negative : index < 0
  · have body := evaluate_checkedStringRead_outOfBounds target trace env str.explode index (Or.inl negative)
    simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData,
      FlatSem.readIndexed, FlatSem.boundsFailure, negative, body, states, EvalResultRel.raise exception]
  · cases element : str.explode[index.toNat]? with
    | none =>
      have bound : str.explode.length ≤ index.toNat := List.getElem?_eq_none_iff.mp element
      have body := evaluate_checkedStringRead_outOfBounds target trace env str.explode index (Or.inr bound)
      simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData,
        FlatSem.readIndexed, FlatSem.boundsFailure, negative, element, body, states, EvalResultRel.raise exception]
    | some byte =>
      have body := evaluate_checkedStringRead_inBounds target trace env str.explode index byte negative element
      simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData,
        FlatSem.readIndexed, negative, element, body, states, EvalResultRel.value (.cons (ValueRel.char byte) .nil)]


/-- Checked string reads reject any argument count other than two. -/
theorem checkedStringRead_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 2) :
    (FlatSem.applyResult state (.src .strsub) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData]
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData]
    | cons second rest =>
      cases rest with
      | nil => simp at wrong
      | cons third rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData]

/-- Checked string indexing simulates the source expression for arbitrary
argument lists whenever the source does not report a type error. -/
theorem evaluate_checkedStringRead {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src .strsub) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src .strsub) args] := by
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have closFix := ClosSem.fixClock_evaluate (compileExps names args).reverse values target
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate]
    simp only [flatFix, failure]
  have argsSim := argsSim argsNotTypeError
  unfold EvalSim at argsSim ⊢
  simp only [compile, compileExps, compileExp, compileOp] at ⊢
  simp only [compile, compileExps_reverse] at argsSim
  rw [FlatSem.evaluate, ClosSem.evaluate, closFix]
  simp only [flatFix]
  cases flatRun : FlatSem.evaluate env source args.reverse with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate (compileExps names args).reverse values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at argsSim ⊢
      rcases argsSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        rename_i sourceArgs targetArgs
        have resultShape : (FlatSem.applyResult next (.src .strsub) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 2 := by
          by_contra wrong
          apply resultShape
          apply checkedStringRead_wrong_arity
          simpa using wrong
        cases related with
        | nil => simp at length
        | cons indexRel tail =>
          cases tail with
          | nil => simp at length
          | cons pointerRel tail =>
            cases tail with
            | cons _ _ => simp at length
            | nil =>
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at resultShape
              cases indexRel <;> cases pointerRel <;>
                simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
                  FlatSem.doAppMemory, FlatSem.doAppData] at resultShape
              case int.string index str =>
                simpa using checkedStringRead_body_related next nextTarget trace values str index states


/-- Vector construction rejects any argument count other than one. -/
theorem vectorFromList_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 1) :
    (FlatSem.applyResult state (.src .vfromList) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData]
  | cons first rest =>
    cases rest with
    | nil => simp at wrong
    | cons second rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData]

/-- Vector construction preserves related list elements after evaluating arbitrary
argument lists, provided the source application avoids a type error. -/
theorem evaluate_vectorFromList {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src .vfromList) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src .vfromList) args] := by
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have closFix := ClosSem.fixClock_evaluate (compileExps names args).reverse values target
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate]
    simp only [flatFix, failure]
  have argSim := argSim argsNotTypeError
  unfold EvalSim at argSim ⊢
  simp only [compile, compileExps_reverse] at argSim
  simp only [compile, compileExps, compileExp, compileOp] at ⊢
  rw [FlatSem.evaluate, ClosSem.evaluate, closFix]
  simp only [flatFix]
  cases flatRun : FlatSem.evaluate env source args.reverse with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate (compileExps names args).reverse values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at argSim ⊢
      rcases argSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        rename_i sourceArgs targetArgs
        have resultShape : (FlatSem.applyResult next (.src .vfromList) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 1 := by
          by_contra wrong
          apply resultShape
          apply vectorFromList_wrong_arity
          simpa using wrong
        cases related with
        | nil => simp at length
        | cons head tail =>
          cases tail with
          | cons _ _ => simp at length
          | nil =>
            simp only [List.reverse_singleton] at resultShape
            rename_i sourceValue targetValue
            cases decoded : FlatSem.valueToList sourceValue with
            | none =>
              simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                FlatSem.doAppData, decoded] at resultShape
            | some items =>
              obtain ⟨targetItems, targetDecoded, itemRel⟩ := valueToList_related sourceValue targetValue items head decoded
              simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                FlatSem.doAppData, decoded, ClosSem.doApp, ClosSem.applyBlock, targetDecoded, states,
                EvalResultRel.value (.cons (ValueRel.vector itemRel) .nil)]

/-- Exploding bytes yields lists of related characters and closure numbers. -/
theorem explodedChars_related (bytes : List (BitVec 8)) :
    List.Forall₂ ValueRel (bytes.map (FlatSem.Value.litv ∘ Flapjack.AstHOL.Lit.char))
      (bytes.map (fun byte => ClosSem.Value.number byte.toNat)) := by
  induction bytes with
  | nil => exact .nil
  | cons byte rest ih => exact .cons (.char byte) ih


/-- String explosion rejects any argument count other than one. -/
theorem stringExplode_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 1) :
    (FlatSem.applyResult state (.src .explode) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData]
  | cons first rest =>
    cases rest with
    | nil => simp at wrong
    | cons second rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData]

/-- String explosion returns related lists of bytes after evaluating arbitrary
argument lists, provided the source application avoids a type error. -/
theorem evaluate_stringExplode {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src .explode) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src .explode) args] := by
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have closFix := ClosSem.fixClock_evaluate (compileExps names args).reverse values target
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate]
    simp only [flatFix, failure]
  have argSim := argSim argsNotTypeError
  unfold EvalSim at argSim ⊢
  simp only [compile, compileExps_reverse] at argSim
  simp only [compile, compileExps, compileExp, compileOp] at ⊢
  rw [FlatSem.evaluate, ClosSem.evaluate, closFix]
  simp only [flatFix]
  cases flatRun : FlatSem.evaluate env source args.reverse with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate (compileExps names args).reverse values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at argSim ⊢
      rcases argSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        rename_i sourceArgs targetArgs
        have resultShape : (FlatSem.applyResult next (.src .explode) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 1 := by
          by_contra wrong
          apply resultShape
          apply stringExplode_wrong_arity
          simpa using wrong
        cases related with
        | nil => simp at length
        | cons head tail =>
          cases tail with
          | cons _ _ => simp at length
          | nil =>
            simp only [List.reverse_singleton] at resultShape
            cases head <;> simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
              FlatSem.doAppMemory, FlatSem.doAppData] at resultShape
            case string str =>
              have listRel := listToValue_related (explodedChars_related str.explode)
              simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                FlatSem.doAppData, ClosSem.doApp, ClosSem.applyMemory, states,
                EvalResultRel.value (.cons listRel .nil)]

/-- Appending related list values produces related list values. -/
theorem listAppend_related (left right : List FlatSem.Value) (targetLeft targetRight : List ClosSem.Value)
    (leftRel : List.Forall₂ ValueRel left targetLeft) (rightRel : List.Forall₂ ValueRel right targetRight) :
    ValueRel (FlatSem.listToValue (left ++ right)) (ClosSem.listToValue (targetLeft ++ targetRight)) := by
  apply listToValue_related
  induction leftRel with
  | nil => exact rightRel
  | cons head tail ih => exact .cons head ih


/-- List append reject any argument count other than two. -/
theorem listAppend_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 2) :
    (FlatSem.applyResult state (.src .listAppend) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData]
  | cons first rest =>
    cases rest with
    | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData]
    | cons second rest =>
      cases rest with
      | nil => simp at wrong
      | cons third rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData]

/-- List append simulates the source expression for arbitrary
argument lists whenever the source does not report a type error. -/
theorem evaluate_listAppend {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src .listAppend) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src .listAppend) args] := by
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have closFix := ClosSem.fixClock_evaluate (compileExps names args).reverse values target
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate]
    simp only [flatFix, failure]
  have argsSim := argsSim argsNotTypeError
  unfold EvalSim at argsSim ⊢
  simp only [compile, compileExps, compileExp, compileOp] at ⊢
  simp only [compile, compileExps_reverse] at argsSim
  rw [FlatSem.evaluate, ClosSem.evaluate, closFix]
  simp only [flatFix]
  cases flatRun : FlatSem.evaluate env source args.reverse with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate (compileExps names args).reverse values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at argsSim ⊢
      rcases argsSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        rename_i sourceArgs targetArgs
        have resultShape : (FlatSem.applyResult next (.src .listAppend) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 2 := by
          by_contra wrong
          apply resultShape
          apply listAppend_wrong_arity
          simpa using wrong
        cases related with
        | nil => simp at length
        | cons indexRel tail =>
          cases tail with
          | nil => simp at length
          | cons pointerRel tail =>
            cases tail with
            | cons _ _ => simp at length
            | nil =>
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at resultShape
              rename_i sourceRight targetRight sourceLeft targetLeft
              cases leftDecoded : FlatSem.valueToList sourceLeft with
              | none =>
                simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                  FlatSem.doAppData, leftDecoded] at resultShape
              | some left =>
                cases rightDecoded : FlatSem.valueToList sourceRight with
                | none =>
                  simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                    FlatSem.doAppData, leftDecoded, rightDecoded] at resultShape
                | some right =>
                  obtain ⟨targetLeftItems, targetLeftDecoded, leftRel⟩ :=
                    valueToList_related sourceLeft targetLeft left pointerRel leftDecoded
                  obtain ⟨targetRightItems, targetRightDecoded, rightRel⟩ :=
                    valueToList_related sourceRight targetRight right indexRel rightDecoded
                  have resultRel := listAppend_related left right targetLeftItems targetRightItems leftRel rightRel
                  simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                    FlatSem.doAppData, leftDecoded, rightDecoded, ClosSem.doApp, ClosSem.applyBlock,
                    targetLeftDecoded, targetRightDecoded, states, EvalResultRel.value (.cons resultRel .nil)]

end Flapjack.Compiler.Backend.FlatToClos
