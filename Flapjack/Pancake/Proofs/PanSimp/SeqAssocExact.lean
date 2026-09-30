import Flapjack.Pancake.PanSimp
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace Flapjack
open Pancake.PanLang PanSemStateFiniteExact

namespace PanSimpSeqAssocSupport
/-- Imported canonical-state roundtrip infrastructure; no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness
end PanSimpSeqAssocSupport

/-- Local exact Seq association support. No separate HOL declaration names
this equation; it follows directly from source evaluate_def's Seq clause. -/
private theorem evaluateSeqAssociate {width : Nat} {σ : Type} [NeZero width]
    (pre first second : ProgHOL width) (state : PanSemStateFiniteExact width σ) :
    evaluateHOLFiniteState state (.seq (.seq pre first) second) =
      evaluateHOLFiniteState state (.seq pre (.seq first second)) := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_seq_line780,
    evaluateHOLFiniteState_seq_line780]
  generalize evaluateHOLFiniteState state pre = outcome
  rcases outcome with ⟨result, post⟩
  cases result with
  | some result => rfl
  | none =>
    simp only
    rw [evaluateHOLFiniteState_seq_line780]

/-- Genuine source evaluate_seq_assoc Seq case: the only hypotheses are the two
recursive induction hypotheses prescribed by seq_assoc_def. The conclusion is
its full evaluation equality for arbitrary prefix, nested Seq and state. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "evaluate_seq_assoc"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateSeqAssocSeqHOL {width : Nat} {σ : Type} [NeZero width]
    (pre first second : ProgHOL width)
    (hfirst : ∀ state : PanSemStateFiniteExact width σ,
      evaluateHOLFiniteState state (seqAssocHOL pre first) =
        evaluateHOLFiniteState state (.seq pre first))
    (hsecond : ∀ state : PanSemStateFiniteExact width σ,
      evaluateHOLFiniteState state (seqAssocHOL (seqAssocHOL pre first) second) =
        evaluateHOLFiniteState state (.seq (seqAssocHOL pre first) second)) :
    ∀ state : PanSemStateFiniteExact width σ,
      evaluateHOLFiniteState state (seqAssocHOL pre (.seq first second)) =
        evaluateHOLFiniteState state (.seq pre (.seq first second)) := by
  intro state
  rw [seqAssocHOL.eq_3, hsecond]
  rw [evaluateHOLFiniteState_seq_line780, hfirst]
  rw [← evaluateHOLFiniteState_seq_line780]
  exact evaluateSeqAssociate pre first second state

end Flapjack
