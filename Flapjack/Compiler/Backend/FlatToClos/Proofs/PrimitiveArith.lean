import Flapjack.Compiler.Backend.FlatToClos.Proofs.RejectedArith
import Flapjack.Compiler.Backend.FlatToClos.Proofs.WordExpressions
import Flapjack.Compiler.Backend.FlatToClos.Proofs.FloatExpressions

/-! Combined primitive arithmetic simulation for flat-to-closure lowering. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- All primitive arithmetic expressions preserve the proof-side evaluation
relation under the argument induction hypothesis and source non-type-error
condition. The semantic carriers remain subject to HOL correspondence review. -/
theorem evaluate_primitiveArith {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (action : Arith) (typ : PrimType) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.arith action typ)) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.arith action typ)) args] := by
  cases typ with
  | boolT => exact evaluate_boolArith env names values source target trace action args argsSim notTypeError
  | charT => exact evaluate_nonNumericArith env names values source target trace action .charT (Or.inl rfl) args argsSim notTypeError
  | strT => exact evaluate_nonNumericArith env names values source target trace action .strT (Or.inr rfl) args argsSim notTypeError
  | intT =>
    cases action
    all_goals first
      | exact evaluate_intAdd env names values source target trace args argsSim notTypeError
      | exact evaluate_intSub env names values source target trace args argsSim notTypeError
      | exact evaluate_intMul env names values source target trace args argsSim notTypeError
      | exact evaluate_intDiv env names values source target trace args argsSim notTypeError
      | exact evaluate_intMod env names values source target trace args argsSim notTypeError
      | exact evaluate_rejectedIntArith env names values source target trace _ (by decide) args argsSim notTypeError
  | wordT width =>
    by_cases supported : action = .add ∨ action = .sub ∨ action = .and ∨ action = .or ∨ action = .xor
    · exact evaluate_wordArith env names values source target trace action width supported args argsSim notTypeError
    · have invalid : action ≠ .add ∧ action ≠ .sub ∧ action ≠ .and ∧ action ≠ .or ∧ action ≠ .xor := by
        simpa only [not_or] using supported
      exact evaluate_rejectedWordArith env names values source target trace action width invalid args argsSim notTypeError
  | float64T =>
    by_cases supported : action = .abs ∨ action = .neg ∨ action = .sqrt ∨ action = .add ∨
      action = .sub ∨ action = .mul ∨ action = .div ∨ action = .fma
    · exact evaluate_floatArith env names values source target trace action supported args argsSim notTypeError
    · have invalid : action ≠ .abs ∧ action ≠ .neg ∧ action ≠ .sqrt ∧ action ≠ .add ∧
          action ≠ .sub ∧ action ≠ .mul ∧ action ≠ .div ∧ action ≠ .fma := by
        simpa only [not_or] using supported
      exact evaluate_rejectedFloatArith env names values source target trace action invalid args argsSim notTypeError

end Flapjack.Compiler.Backend.FlatToClos
