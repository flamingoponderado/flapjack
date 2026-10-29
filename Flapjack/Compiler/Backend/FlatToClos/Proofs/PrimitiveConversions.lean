import Flapjack.Compiler.Backend.FlatToClos.Proofs.CharConversion
import Flapjack.Compiler.Backend.FlatToClos.Proofs.RejectedConversions

/-! Combined primitive conversion simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- Primitive conversions preserve the proof-side relation under the argument
induction hypothesis and the nested-expression hypotheses required by the
two erased conversion patterns. The semantic carriers await HOL review. -/
theorem evaluate_primitiveConversion {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (sourceType targetType : PrimType) (args : List FlatLang.Exp)
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
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.fromTo sourceType targetType)) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.fromTo sourceType targetType)) args] := by
  by_cases supported : conversionSupported sourceType targetType = true
  · cases sourceType <;> cases targetType <;> simp [conversionSupported] at supported
    all_goals try (rename_i width; cases width <;> simp_all)
    all_goals first
      | exact evaluate_word8ToInt env names values source target trace args argsSim notTypeError
      | exact evaluate_word64ToInt env names values source target trace args argsSim notTypeError
      | exact evaluate_intToWord8 env names values source target trace args argsSim charInnerSim notTypeError
      | exact evaluate_intToWord64 env names values source target trace args argsSim notTypeError
      | exact evaluate_charToInt env names values source target trace args argsSim notTypeError
      | exact evaluate_intToChar env names values source target trace args argsSim wordInnerSim notTypeError
      | exact evaluate_charToWord8 env names values source target trace args argsSim notTypeError
      | exact evaluate_word8ToChar env names values source target trace args argsSim notTypeError
      | exact evaluate_floatToWord64 env names values source target trace args argsSim notTypeError
      | exact evaluate_word64ToFloat env names values source target trace args argsSim notTypeError
  · have invalid : conversionSupported sourceType targetType = false := by
      cases h : conversionSupported sourceType targetType <;> simp_all
    exact evaluate_rejectedConversion env names values source target trace sourceType targetType invalid args argsSim notTypeError

end Flapjack.Compiler.Backend.FlatToClos
