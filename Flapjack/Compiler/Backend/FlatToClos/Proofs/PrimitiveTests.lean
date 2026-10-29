import Flapjack.Compiler.Backend.FlatToClos.Proofs.ByteComparisons
import Flapjack.Compiler.Backend.FlatToClos.Proofs.FloatComparisons
import Flapjack.Compiler.Backend.FlatToClos.Proofs.StringComparisons
import Flapjack.Compiler.Backend.FlatToClos.Proofs.RejectedComparisons

/-! Combined simulation for source primitive tests. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL

/-- All primitive test expressions preserve the proof-side evaluation
relations under the source non-type-error condition and the argument
induction hypothesis. The semantic carriers still await HOL correspondence
review. -/
theorem evaluate_primitiveTest {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option Flapjack.Basis.Pure.MlString.MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (test : Test) (typ : PrimType) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.test test typ)) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.test test typ)) args] := by
  cases test with
  | equal => exact evaluate_primitiveEquality env names values source target trace typ args argsSim notTypeError
  | compare cmp =>
    cases typ with
    | boolT => exact evaluate_invalidCompare env names values source target trace cmp .boolT (Or.inl rfl) args argsSim notTypeError
    | intT => exact evaluate_intCompare env names values source target trace cmp args argsSim notTypeError
    | charT => exact evaluate_charCompare env names values source target trace cmp args argsSim notTypeError
    | strT => exact evaluate_stringCompare env names values source target trace cmp args argsSim notTypeError
    | float64T => exact evaluate_float64Compare env names values source target trace cmp args argsSim notTypeError
    | wordT size =>
      cases size with
      | w8 => exact evaluate_word8Compare env names values source target trace cmp args argsSim notTypeError
      | w64 => exact evaluate_invalidCompare env names values source target trace cmp (.wordT .w64) (Or.inr rfl) args argsSim notTypeError
  | altCompare cmp =>
    by_cases isString : typ = .strT
    · subst typ
      exact evaluate_stringAltCompare env names values source target trace cmp args argsSim notTypeError
    · exact evaluate_nonStringAltCompare env names values source target trace cmp typ isString args argsSim notTypeError

end Flapjack.Compiler.Backend.FlatToClos
