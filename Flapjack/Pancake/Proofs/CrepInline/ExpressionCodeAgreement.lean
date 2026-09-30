import Flapjack.Pancake.Proofs.CrepInline

namespace Flapjack.CrepInlineExpressionCodeAgreement
open Flapjack.CrepInlineExact

/-- Canonical finite-support state roundtrip for the representation qualifier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

/-- Source-shaped success preservation. The code-domain inclusion is retained
as in HOL: membership in FDOM is lookup ≠ none on the canonical map.
The only carrier translations are canonical finite-support maps and positive
width-indexed words (with universe-0 FFI host). This proof reuses the stronger
Flapjack-only Option-equality helper without tagging that helper as this source
theorem. The reviewed expression evaluator does not inspect code. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "eval_state_locals_same_code_fdom_same"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem evalStateLocalsSameCodeFdomSame {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (expression : CrepExpHOL width)
    (value : HolWordLab width) (target : CrepSemHOLState width σ)
    (h : evalCrepSemHOLExp state expression = some value ∧
      crepInlineStateRelCodeExact state target ∧
      crepInlineLocalsStrongRelExact state target ∧
      (∀ name, state.code.lookup name ≠ none → target.code.lookup name ≠ none)) :
    evalCrepSemHOLExp target expression = some value := by
  rw [← evalCrepSemHOLExp_state_rel_code_exact state target expression h.2.1 h.2.2.1 h.2.2.2]
  exact h.1

end Flapjack.CrepInlineExpressionCodeAgreement
