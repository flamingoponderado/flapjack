import Flapjack.Pancake.Semantics.PanProps.EvalInvariant
namespace Flapjack.Pancake.Proofs.PanStructs.EvaluateStructsCodeInvariant
open Flapjack
open Flapjack.Pancake.PanLang
/-- Canonical imported state-carrier roundtrip for this representation qualifier.
Flapjack infrastructure, not an independent HOL declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness


/-- Full original local structural/code invariant. The result equation is the
sole premise; both fields are preserved on every evaluation outcome. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "evaluate_structs_code_inv"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateStructsCodeInv {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) (source post : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width))
    (heval : PanSemStateFiniteExact.evaluateHOLFiniteState source program = (res, post)) :
    post.structs = source.structs ∧ post.code = source.code := by
  classical
  have hevalProps : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
      (PanPropsEvalStateFiniteExact.ofPanSemFinite source) program =
      (res, PanPropsEvalStateFiniteExact.ofPanSemFinite post) := by
    simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair] using
      congrArg (fun pair => (pair.1, PanPropsEvalStateFiniteExact.ofPanSemFinite pair.2)) heval
  have hinv := evaluateInvariantsHOLFinite program
    (PanPropsEvalStateFiniteExact.ofPanSemFinite source) res
    (PanPropsEvalStateFiniteExact.ofPanSemFinite post) hevalProps
  exact ⟨hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2.1⟩
end Flapjack.Pancake.Proofs.PanStructs.EvaluateStructsCodeInvariant
