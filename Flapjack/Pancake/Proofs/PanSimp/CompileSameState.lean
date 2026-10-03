import Flapjack.Pancake.Proofs.PanSimp.RetToTailAssembly

/-!
Original pan_simp evaluation lemmas around the whole compiler
`compile p = ret_to_tail (seq_assoc Skip p)` (pan_simpProofScript.sml:103-115,
163-180, 347-362): `evaluate_while_no_error_imp`, `eval_seq_assoc_eq_evaluate`,
`eval_seq_assoc_not_error`, `compile_correct_same_state` and
`evaluate_seq_simp`.
-/

namespace Flapjack.PanSimp

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open PanSemStateFiniteExact
open Flapjack.PanSimp.RetToTailCorrect

namespace CompileSameStateSupport
/-- Imported canonical-state roundtrip infrastructure; no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness
end CompileSameStateSupport

@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "evaluate_while_no_error_imp"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateWhileNoErrorImpHOL {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (e : ExpHOL width) (w : BitVec width)
    (c : ProgHOL width) :
    @evalHOLExact width σ _ s.toExact
        (fun address => Classical.propDecidable (s.memaddrs address)) e =
        some (.val (.word w)) ∧ w ≠ 0 ∧ s.clock ≠ 0 ∧
      (evaluateHOLFiniteState s (.while e c)).1 ≠ some .error →
    (evaluateHOLFiniteState (decClockHOLFinite s) c).1 ≠ some .error := by
  rintro ⟨hev, hw, hc, h⟩ hb
  apply h
  rw [evaluateHOLFiniteState_while_fixClockRewrite]
  have hev' : @evalHOLFinite width σ _ s
      (fun address => Classical.propDecidable (s.memaddrs address)) e =
      some (.val (.word w)) := hev
  rw [hev']
  simp only [if_pos hw, if_neg hc, hb]

@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "eval_seq_assoc_eq_evaluate"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evalSeqAssocEqEvaluateHOL {width : Nat} {σ : Type} [NeZero width]
    (p : ProgHOL width) (s t : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) :
    evaluateHOLFiniteState s (seqAssocHOL .skip p) = (res, t) →
      evaluateHOLFiniteState s p = (res, t) := by
  rw [evaluateSeqAssocHOL, evaluateSkipSeqHOL]
  exact id

@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "eval_seq_assoc_not_error"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evalSeqAssocNotErrorHOL {width : Nat} {σ : Type} [NeZero width]
    (p : ProgHOL width) (s : PanSemStateFiniteExact width σ) :
    (evaluateHOLFiniteState s p).1 ≠ some .error →
      (evaluateHOLFiniteState s (seqAssocHOL .skip p)).1 ≠ some .error := by
  rw [evaluateSeqAssocHOL, evaluateSkipSeqHOL]
  exact id

@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "compile_correct_same_state"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileCorrectSameStateHOL {width : Nat} {σ : Type} [NeZero width]
    (p : ProgHOL width) (s : PanSemStateFiniteExact width σ) :
    (evaluateHOLFiniteState s p).1 ≠ some .error →
      evaluateHOLFiniteState s (panSimpCompileHOL p) = evaluateHOLFiniteState s p := by
  intro h
  unfold panSimpCompileHOL
  rw [retToTailCorrectHOL _ s (evalSeqAssocNotErrorHOL p s h), evaluateSeqAssocHOL,
    evaluateSkipSeqHOL]

@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "evaluate_seq_simp"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateSeqSimpHOL {width : Nat} {σ : Type} [NeZero width]
    (p : ProgHOL width) (s t : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) :
    evaluateHOLFiniteState s p = (res, t) ∧ res ≠ some .error →
      evaluateHOLFiniteState s (panSimpCompileHOL p) = (res, t) := by
  rintro ⟨h, hres⟩
  rw [compileCorrectSameStateHOL p s (by rw [h]; exact hres), h]

end Flapjack.PanSimp
