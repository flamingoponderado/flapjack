import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Misc.OptMmapCong

namespace Flapjack.CrepInlineClockExpressions

/-- Canonical finite-support state roundtrip for the representation qualifier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness



/-- Source expression evaluation ignores the clock; no success assumption. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "eval_dec_clock_eq"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem evalDecClockEq {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (expression : CrepExpHOL width) :
    evalCrepSemHOLExp (decClockCrepSemHOL state) expression =
      evalCrepSemHOLExp state expression := by
  fun_induction evalCrepSemHOLExp state expression with
  | case7 _ args ih | case8 _ args ih =>
      simp only [evalCrepSemHOLExp]
      rw [optMmapCongHOL args args _ _ rfl ih]
  | _ => simp_all [evalCrepSemHOLExp, decClockCrepSemHOL]

/-- Source OPT_MMAP equation, retaining failure as well as success. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "opt_mmap_eval_dec_clock_eq"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem optMmapEvalDecClockEq {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (expressions : List (CrepExpHOL width)) :
    expressions.mapM (evalCrepSemHOLExp (decClockCrepSemHOL state)) =
      expressions.mapM (evalCrepSemHOLExp state) := by
  have h : evalCrepSemHOLExp (decClockCrepSemHOL state) = evalCrepSemHOLExp state := by
    funext expression
    exact evalDecClockEq state expression
  rw [h]

end Flapjack.CrepInlineClockExpressions
