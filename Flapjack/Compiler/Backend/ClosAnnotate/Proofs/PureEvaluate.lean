module

public import Flapjack.Compiler.Backend.Semantics.ClosProps.PureEvaluate

@[expose] public section

/-! Pure evaluation used by the closure annotation correctness proof. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL (Result)

namespace PureEvaluatePort
/-- The closure state uses canonical finite-support maps. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end PureEvaluatePort

/-- A non-type-error evaluation of pure expressions returns one value per
expression and preserves the state. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "evaluate_pure_IMP"
  (fmap_as_finite_support := [refs, code])]
theorem evaluatePureImp {C F : Type} (expressions : List ClosLang.Exp) (env : List Value)
    (source : State C F) (result : Result (List Value) Value) (next : State C F)
    (h : evaluate expressions env source = (result, next) ∧
      (∀ expression ∈ expressions, ClosLang.pure expression = true) ∧
      result ≠ .err (.abort .typeError)) :
    ∃ values, result = .val values ∧ next = source ∧ values.length = expressions.length := by
  have correct := everyPureCorrect expressions env source h.2.1
  rw [h.1] at correct
  cases result with
  | val values => exact ⟨values, rfl, correct.1, correct.2⟩
  | err error =>
    cases error with
    | raise value => exact False.elim correct
    | abort abort => cases correct; exact False.elim (h.2.2 rfl)

end Flapjack.Compiler.Backend.ClosAnnotate
