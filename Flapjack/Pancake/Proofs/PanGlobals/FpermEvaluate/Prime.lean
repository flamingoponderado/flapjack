import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Assembly

namespace Flapjack
open Pancake.PanLang PanSemStateFiniteExact

namespace FpermPrimeSupport
/-- Imported canonical-state roundtrip infrastructure; no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness
end FpermPrimeSupport

/-- Original clock-update corollary of function permutation. It maps the complete
result/post-state pair for an arbitrary program and clock, with no successful-run,
non-error, induction-hypothesis or target-evaluation premise. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fperm'"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFpermPrimeHOL {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (program : ProgHOL width) (state : PanSemStateFiniteExact width σ)
    (clock : Nat) :
    evaluateHOLFiniteState { state with code := fpermCodeHOL f g state.code, clock := clock }
      (fpermHOL f g program) =
      (fun outcome : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ =>
        (outcome.1, { outcome.2 with code := fpermCodeHOL f g outcome.2.code }))
        (evaluateHOLFiniteState { state with clock := clock } program) := by
  generalize heval : evaluateHOLFiniteState { state with clock := clock } program = outcome
  rcases outcome with ⟨res, post⟩
  exact evaluateFpermHOL f g program { state with clock := clock } res post heval

end Flapjack
