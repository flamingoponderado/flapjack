import Flapjack.Compiler.Backend.FlatToClos.Proofs.BooleanExpressions

/-! Unsupported arithmetic cases in flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- The source numeric dispatcher rejects unsupported integer actions. -/
theorem intNumericCore_rejects {F : Type} (state : Store Value × HolFfiState F)
    (action : Arith)
    (invalid : action ≠ .add ∧ action ≠ .sub ∧ action ≠ .mul ∧ action ≠ .div ∧ action ≠ .mod)
    (values : List Value) :
    SemanticPrimitivesHOL.doAppNumericCore state (.arith action .intT) values = some none := by
  cases values with
  | nil => cases action <;> simp_all [SemanticPrimitivesHOL.doAppNumericCore]
  | cons first tail =>
    cases tail with
    | nil => cases action <;> simp_all [SemanticPrimitivesHOL.doAppNumericCore]
    | cons second tail =>
      cases tail with
      | cons _ _ => cases action <;> simp_all [SemanticPrimitivesHOL.doAppNumericCore]
      | nil =>
        cases first <;> cases second <;> cases action <;>
          simp_all [SemanticPrimitivesHOL.doAppNumericCore]
        all_goals
          rename_i left right
          cases left <;> cases right <;> simp

/-- Unsupported integer arithmetic rejects all flat argument lists. -/
theorem intArith_rejects {C F : Type} (state : FlatSem.State C F) (action : Arith)
    (invalid : action ≠ .add ∧ action ≠ .sub ∧ action ≠ .mul ∧ action ≠ .div ∧ action ≠ .mod)
    (args : List FlatSem.Value) :
    (FlatSem.applyResult state (.src (.arith action .intT)) args).2 = .err (.abort .typeError) := by
  have core := intNumericCore_rejects ([], state.ffi) action invalid (args.map FlatSem.flatToValue)
  simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection,
    SemanticPrimitivesHOL.doApp, core]

/-- Unsupported integer arithmetic preserves errors raised by its arguments. -/
theorem evaluate_rejectedIntArith {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (action : Arith)
    (invalid : action ≠ .add ∧ action ≠ .sub ∧ action ≠ .mul ∧ action ≠ .div ∧ action ≠ .mod)
    (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.arith action .intT)) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.arith action .intT)) args] := by
  apply evaluate_rejectedArithFallback env names values source target trace action .intT
  · intro xs
    cases action <;> simp_all [compileArith]
  · intro state args
    exact intArith_rejects state action invalid args
  · exact argsSim
  · exact notTypeError

/-- The source numeric dispatcher rejects unsupported word actions. -/
theorem wordNumericCore_rejects {F : Type} (state : Store Value × HolFfiState F)
    (action : Arith)
    (invalid : action ≠ .add ∧ action ≠ .sub ∧ action ≠ .and ∧ action ≠ .or ∧ action ≠ .xor)
    (width : WordSize) (values : List Value) :
    SemanticPrimitivesHOL.doAppNumericCore state (.arith action (.wordT width)) values = some none := by
  cases width <;> cases values with
  | nil => cases action <;> simp_all [SemanticPrimitivesHOL.doAppNumericCore]
  | cons first tail =>
    cases tail with
    | nil => cases action <;> simp_all [SemanticPrimitivesHOL.doAppNumericCore]
    | cons second tail =>
      cases tail with
      | cons _ _ => cases action <;> simp_all [SemanticPrimitivesHOL.doAppNumericCore]
      | nil =>
        cases first <;> cases second <;> cases action <;>
          simp_all [SemanticPrimitivesHOL.doAppNumericCore]
        all_goals
          rename_i left right
          cases left <;> cases right <;> simp [SemanticPrimitivesHOL.wordArith]

/-- Unsupported word arithmetic rejects all flat argument lists. -/
theorem wordArith_rejects {C F : Type} (state : FlatSem.State C F) (action : Arith) (width : WordSize)
    (invalid : action ≠ .add ∧ action ≠ .sub ∧ action ≠ .and ∧ action ≠ .or ∧ action ≠ .xor)
    (args : List FlatSem.Value) :
    (FlatSem.applyResult state (.src (.arith action (.wordT width))) args).2 = .err (.abort .typeError) := by
  have core := wordNumericCore_rejects ([], state.ffi) action invalid width (args.map FlatSem.flatToValue)
  simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection,
    SemanticPrimitivesHOL.doApp, core]

/-- Unsupported word arithmetic preserves errors raised by its arguments. -/
theorem evaluate_rejectedWordArith {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (action : Arith) (width : WordSize)
    (invalid : action ≠ .add ∧ action ≠ .sub ∧ action ≠ .and ∧ action ≠ .or ∧ action ≠ .xor)
    (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.arith action (.wordT width))) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.arith action (.wordT width))) args] := by
  apply evaluate_rejectedArithFallback env names values source target trace action (.wordT width)
  · intro xs
    cases action <;> simp_all [compileArith]
  · intro state args
    exact wordArith_rejects state action width invalid args
  · exact argsSim
  · exact notTypeError

/-- Unsupported floating-point arithmetic rejects all flat argument lists. -/
theorem floatArith_rejects {C F : Type} (state : FlatSem.State C F) (action : Arith)
    (invalid : action ≠ .abs ∧ action ≠ .neg ∧ action ≠ .sqrt ∧ action ≠ .add ∧
      action ≠ .sub ∧ action ≠ .mul ∧ action ≠ .div ∧ action ≠ .fma)
    (args : List FlatSem.Value) :
    (FlatSem.applyResult state (.src (.arith action .float64T)) args).2 = .err (.abort .typeError) := by
  cases action <;> simp_all [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
    FlatSem.applyNumericProjection, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.floatArith]

/-- Unsupported floating-point arithmetic preserves argument errors. -/
theorem evaluate_rejectedFloatArith {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (action : Arith)
    (invalid : action ≠ .abs ∧ action ≠ .neg ∧ action ≠ .sqrt ∧ action ≠ .add ∧
      action ≠ .sub ∧ action ≠ .mul ∧ action ≠ .div ∧ action ≠ .fma)
    (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.arith action .float64T)) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.arith action .float64T)) args] := by
  apply evaluate_rejectedArithFallback env names values source target trace action .float64T
  · intro xs
    cases action <;> simp_all [compileArith]
  · intro state args
    exact floatArith_rejects state action invalid args
  · exact argsSim
  · exact notTypeError

end Flapjack.Compiler.Backend.FlatToClos
