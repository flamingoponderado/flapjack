import Flapjack.Compiler.Backend.FlatToClos.Proofs.Identity
import Flapjack.Compiler.Backend.FlatToClos.Proofs.ApplicationOperators
import Flapjack.Compiler.Backend.FlatToClos.Proofs.Array
import Flapjack.Compiler.Backend.FlatToClos.Proofs.Memory
import Flapjack.Compiler.Backend.FlatToClos.Proofs.EvaluateCases

/-! Dispatcher for ordinary source operators in the proof-side simulation.
The special application, assignment, dynamic installation, and thunk forcing cases
require additional induction hypotheses. This is not a reviewed HOL port. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- Ordinary source operator compilation preserves the proof-side evaluator
relation, assuming the argument and nested conversion expressions simulate. -/
theorem evaluate_directSourceOp {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (op : AstHOL.Op) (args : List FlatLang.Exp)
    (exclusions : op ≠ .opapp ∧ op ≠ .eval ∧ op ≠ .thunkOp .forceThunk)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (charInnerSim : ∀ innerTrace inner,
      args = [.app innerTrace (.src (.fromTo .charT .intT)) [inner]] →
      (FlatSem.evaluate env source [inner]).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target [inner])
    (wordInnerSim : ∀ innerTrace inner,
      args = [.app innerTrace (.src (.fromTo (.wordT .w8) .intT)) [inner]] →
      (FlatSem.evaluate env source [inner]).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target [inner])
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src op) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src op) args] := by
  cases found : destNop (.src op) args with
  | none =>
    apply evalSim_app_of_op env names values source target trace (.src op) args
      found (by simpa using exclusions.1) (by simpa using exclusions.2.1)
      (by simpa using exclusions.2.2) ?_ argsSim notTypeError
    intro s vs sNext result tNext xs db t ws tt premises
    exact compileOpCorrect s _ vs sNext result tNext xs db t ws tt premises
  | some inner =>
    rcases destNop_shape _ _ _ found with ⟨innerTrace, opEq, shape⟩ | ⟨innerTrace, opEq, shape⟩
    · have innerNotTypeError : (FlatSem.evaluate env source [inner]).2 ≠ .err (.abort .typeError) := by
        intro failed
        apply notTypeError
        cases opEq
        rw [shape, evaluate_flat_conversion, evaluate_flat_conversion]
        cases run : FlatSem.evaluate env source [inner] with
        | mk next result => simp_all
      have simulated := charInnerSim innerTrace inner shape innerNotTypeError
      cases opEq
      subst args
      exact evaluate_char_word_nop env names values source target trace innerTrace inner simulated notTypeError
    · have innerNotTypeError : (FlatSem.evaluate env source [inner]).2 ≠ .err (.abort .typeError) := by
        intro failed
        apply notTypeError
        cases opEq
        rw [shape, evaluate_flat_conversion, evaluate_flat_conversion]
        cases run : FlatSem.evaluate env source [inner] with
        | mk next result => simp_all
      have simulated := wordInnerSim innerTrace inner shape innerNotTypeError
      cases opEq
      subst args
      exact evaluate_word_char_nop env names values source target trace innerTrace inner simulated notTypeError

end Flapjack.Compiler.Backend.FlatToClos
