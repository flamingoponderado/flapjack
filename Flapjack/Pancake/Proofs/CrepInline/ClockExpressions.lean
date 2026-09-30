import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL

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
  change evalCrepSemHOLExp { state with clock := state.clock - 1 } expression =
    evalCrepSemHOLExp state expression
  refine CrepExpHOL.rec
    (motive_1 := fun expression =>
      evalCrepSemHOLExp { state with clock := state.clock - 1 } expression =
        evalCrepSemHOLExp state expression)
    (motive_2 := fun expressions =>
      expressions.mapM (evalCrepSemHOLExp { state with clock := state.clock - 1 }) =
        expressions.mapM (evalCrepSemHOLExp state))
    (fun value => by simp [evalCrepSemHOLExp])
    (fun name => by simp [evalCrepSemHOLExp])
    (fun address ih => by simp [evalCrepSemHOLExp, ih])
    (fun address ih => by simp [evalCrepSemHOLExp, ih])
    (fun address ih => by simp [evalCrepSemHOLExp, ih])
    (fun address => by simp [evalCrepSemHOLExp])
    (fun operator args ih => by simp [evalCrepSemHOLExp, ih])
    (fun operator args ih => by simp [evalCrepSemHOLExp, ih])
    (fun operator left right ihl ihr => by simp [evalCrepSemHOLExp, ihl, ihr])
    (fun operator left right ihl ihr => by simp [evalCrepSemHOLExp, ihl, ihr])
    (by simp [evalCrepSemHOLExp])
    (by simp [evalCrepSemHOLExp])
    (by simp only [List.mapM_nil])
    (fun head tail ihh iht => by simp only [List.mapM_cons, ihh, iht])
    expression

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
