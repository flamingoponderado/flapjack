import Flapjack.Compiler.Backend.FlatToClos.Proofs.Conversions

/-! Unsupported primitive conversions in the flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- Source primitive type pairs accepted by the conversion dispatcher. -/
def conversionSupported : PrimType → PrimType → Bool
  | .wordT .w8, .intT | .wordT .w64, .intT
  | .intT, .wordT .w8 | .intT, .wordT .w64
  | .charT, .intT | .intT, .charT
  | .charT, .wordT .w8 | .wordT .w8, .charT
  | .float64T, .wordT .w64 | .wordT .w64, .float64T => true
  | _, _ => false

/-- The source dispatcher rejects every unsupported type pair. -/
theorem conversionCore_rejects {F : Type} (state : Store Value × HolFfiState F)
    (sourceType targetType : PrimType) (invalid : conversionSupported sourceType targetType = false)
    (values : List Value) :
    SemanticPrimitivesHOL.doAppNumericCore state (.fromTo sourceType targetType) values = some none := by
  cases sourceType <;> cases targetType <;> simp_all [conversionSupported, SemanticPrimitivesHOL.doAppNumericCore]
  all_goals
    rename_i width
    cases width <;> simp_all

/-- Unsupported type pairs use the compiler fallback, including before the
special syntactic conversion optimizations are considered. -/
theorem compile_rejectedConversion (names : List (Option MlString)) (trace : BackendCommon.Tra)
    (sourceType targetType : PrimType) (invalid : conversionSupported sourceType targetType = false)
    (args : List FlatLang.Exp) :
    compileExp names (.app trace (.src (.fromTo sourceType targetType)) args) =
      .let .none (compileExps names args).reverse (.var .none 0) := by
  cases sourceType <;> cases targetType <;> simp_all [conversionSupported, compileExp, compileOp]
  all_goals
    rename_i width
    cases width <;> simp_all

/-- Unsupported conversion type pairs fail for all flat argument lists. -/
theorem conversion_rejects {C F : Type} (state : FlatSem.State C F) (sourceType targetType : PrimType)
    (invalid : conversionSupported sourceType targetType = false) (args : List FlatSem.Value) :
    (FlatSem.applyResult state (.src (.fromTo sourceType targetType)) args).2 = .err (.abort .typeError) := by
  have core := conversionCore_rejects ([], state.ffi) sourceType targetType invalid (args.map FlatSem.flatToValue)
  simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection,
    SemanticPrimitivesHOL.doApp, core]

/-- A rejected conversion simulates the source expression for arbitrary
argument lists whenever the source does not report a type error. -/
theorem evaluate_rejectedConversion {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (sourceType targetType : PrimType)
    (invalid : conversionSupported sourceType targetType = false)
    (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.fromTo sourceType targetType)) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.fromTo sourceType targetType)) args] := by
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have closFix := ClosSem.fixClock_evaluate (compileExps names args).reverse values target
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate]
    simp only [flatFix, failure]
  have argsSim := argsSim argsNotTypeError
  have compiled := compile_rejectedConversion names trace sourceType targetType invalid args
  unfold EvalSim at argsSim ⊢
  simp only [compile, compileExps, compiled] at ⊢
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
        have resultShape : (FlatSem.applyResult next (.src (.fromTo sourceType targetType)) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        exact False.elim (resultShape (conversion_rejects next sourceType targetType invalid sourceArgs.reverse))

end Flapjack.Compiler.Backend.FlatToClos
