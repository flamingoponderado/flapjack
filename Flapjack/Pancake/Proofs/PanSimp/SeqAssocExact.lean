import Flapjack.Pancake.Proofs.PanSimp.SkipSeqExact
import Flapjack.Pancake.Proofs.PanSimp.WhileBodyExact
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

/-- Local complete Seq congruence in its second program. No separate HOL
original: direct infrastructure from the exact Seq equation. -/
private theorem evaluateSeqSecondCongr {width : Nat} {σ : Type} [NeZero width]
    (pre first second : ProgHOL width)
    (h : ∀ state : PanSemStateFiniteExact width σ,
      evaluateHOLFiniteState state first = evaluateHOLFiniteState state second)
    (state : PanSemStateFiniteExact width σ) :
    evaluateHOLFiniteState state (.seq pre first) =
      evaluateHOLFiniteState state (.seq pre second) := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_seq_line780]
  generalize evaluateHOLFiniteState state pre = outcome
  rcases outcome with ⟨result, post⟩
  cases result with
  | none => exact h post
  | some result => rfl

/-- Genuine source Dec recursion case with only its source body IH; complete
post-state equality includes restoration of the caller's local binding. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "evaluate_seq_assoc"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateSeqAssocDecHOL {width : Nat} {σ : Type} [NeZero width]
    (pre body : ProgHOL width) (name : MlS) (shape : ShapeHOL) (value : ExpHOL width)
    (hbody : ∀ state : PanSemStateFiniteExact width σ,
      evaluateHOLFiniteState state (seqAssocHOL .skip body) =
        evaluateHOLFiniteState state (.seq .skip body)) :
    ∀ state : PanSemStateFiniteExact width σ,
      evaluateHOLFiniteState state (seqAssocHOL pre (.dec name shape value body)) =
        evaluateHOLFiniteState state (.seq pre (.dec name shape value body)) := by
  have hb : ∀ state : PanSemStateFiniteExact width σ,
      evaluateHOLFiniteState state (seqAssocHOL .skip body) =
        evaluateHOLFiniteState state body := by
    intro state
    rw [hbody, evaluateSkipSeqHOL]
  intro state
  rw [seqAssocHOL.eq_2, evaluateSmartSeqHOL]
  apply evaluateSeqSecondCongr
  intro post
  rw [evaluateHOLFiniteState_dec_total, evaluateHOLFiniteState_dec_total]
  simp only [hb]

/-- Genuine source If recursion case with the two branch IHs from HOL; no
successful condition or chosen-branch premise is added. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "evaluate_seq_assoc"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateSeqAssocIfHOL {width : Nat} {σ : Type} [NeZero width]
    (pre thenBranch elseBranch : ProgHOL width) (condition : ExpHOL width)
    (hthen : ∀ state : PanSemStateFiniteExact width σ,
      evaluateHOLFiniteState state (seqAssocHOL .skip thenBranch) =
        evaluateHOLFiniteState state (.seq .skip thenBranch))
    (helse : ∀ state : PanSemStateFiniteExact width σ,
      evaluateHOLFiniteState state (seqAssocHOL .skip elseBranch) =
        evaluateHOLFiniteState state (.seq .skip elseBranch)) :
    ∀ state : PanSemStateFiniteExact width σ,
      evaluateHOLFiniteState state (seqAssocHOL pre (.ite condition thenBranch elseBranch)) =
        evaluateHOLFiniteState state (.seq pre (.ite condition thenBranch elseBranch)) := by
  have ht : ∀ state : PanSemStateFiniteExact width σ,
      evaluateHOLFiniteState state (seqAssocHOL .skip thenBranch) =
        evaluateHOLFiniteState state thenBranch := by
    intro state
    rw [hthen, evaluateSkipSeqHOL]
  have he : ∀ state : PanSemStateFiniteExact width σ,
      evaluateHOLFiniteState state (seqAssocHOL .skip elseBranch) =
        evaluateHOLFiniteState state elseBranch := by
    intro state
    rw [helse, evaluateSkipSeqHOL]
  intro state
  rw [seqAssocHOL.eq_4, evaluateSmartSeqHOL]
  apply evaluateSeqSecondCongr
  intro post
  rw [evaluateHOLFiniteState_ite, evaluateHOLFiniteState_ite]
  simp only [ht, he]

/-- Genuine source While recursion case with only its body IH. The accepted
unconditional While congruence preserves every source clock/control case. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "evaluate_seq_assoc"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateSeqAssocWhileHOL {width : Nat} {σ : Type} [NeZero width]
    (pre body : ProgHOL width) (condition : ExpHOL width)
    (hbody : ∀ state : PanSemStateFiniteExact width σ,
      evaluateHOLFiniteState state (seqAssocHOL .skip body) =
        evaluateHOLFiniteState state (.seq .skip body)) :
    ∀ state : PanSemStateFiniteExact width σ,
      evaluateHOLFiniteState state (seqAssocHOL pre (.while condition body)) =
        evaluateHOLFiniteState state (.seq pre (.while condition body)) := by
  have hb : ∀ state : PanSemStateFiniteExact width σ,
      evaluateHOLFiniteState state (seqAssocHOL .skip body) =
        evaluateHOLFiniteState state body := by
    intro state
    rw [hbody, evaluateSkipSeqHOL]
  intro state
  rw [seqAssocHOL.eq_5, evaluateSmartSeqHOL]
  exact evaluateSeqSecondCongr pre _ _
    (evaluateWhileBodySameHOL _ _ condition hb) state

/-- Genuine Call-handler source case with only the handler IH. Exception
selection, shape checks and caller local binding remain literal. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "evaluate_seq_assoc"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateSeqAssocCallHandlerHOL {width : Nat} {σ : Type} [NeZero width]
    (pre handler : ProgHOL width) (returns : Option (VarKind × MlS))
    (exception handlerVar function : MlS) (arguments : List (ExpHOL width))
    (hhandler : ∀ state : PanSemStateFiniteExact width σ,
      evaluateHOLFiniteState state (seqAssocHOL .skip handler) =
        evaluateHOLFiniteState state (.seq .skip handler)) :
    ∀ state : PanSemStateFiniteExact width σ,
      evaluateHOLFiniteState state
        (seqAssocHOL pre (.call (some (returns, some (exception, handlerVar, handler)))
          function arguments)) =
        evaluateHOLFiniteState state (.seq pre
          (.call (some (returns, some (exception, handlerVar, handler))) function arguments)) := by
  have hh : ∀ state : PanSemStateFiniteExact width σ,
      evaluateHOLFiniteState state (seqAssocHOL .skip handler) =
        evaluateHOLFiniteState state handler := by
    intro state
    rw [hhandler, evaluateSkipSeqHOL]
  intro state
  rw [seqAssocHOL.eq_8]
  rw [evaluateSmartSeqHOL]
  apply evaluateSeqSecondCongr
  intro post
  rw [evaluateHOLFiniteState_call, evaluateHOLFiniteState_call]
  cases returns with
  | none => simp only [hh]
  | some resultVar =>
    rcases resultVar with ⟨kind, name⟩
    simp only [hh]

/-- Genuine DecCall source case with only its continuation IH. Return-shape
checks and complete local restoration remain literal. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "evaluate_seq_assoc"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateSeqAssocDecCallHOL {width : Nat} {σ : Type} [NeZero width]
    (pre continuation : ProgHOL width) (name : MlS) (shape : ShapeHOL)
    (function : MlS) (arguments : List (ExpHOL width))
    (hcontinuation : ∀ state : PanSemStateFiniteExact width σ,
      evaluateHOLFiniteState state (seqAssocHOL .skip continuation) =
        evaluateHOLFiniteState state (.seq .skip continuation)) :
    ∀ state : PanSemStateFiniteExact width σ,
      evaluateHOLFiniteState state
        (seqAssocHOL pre (.decCall name shape function arguments continuation)) =
        evaluateHOLFiniteState state (.seq pre
          (.decCall name shape function arguments continuation)) := by
  have hc : ∀ state : PanSemStateFiniteExact width σ,
      evaluateHOLFiniteState state (seqAssocHOL .skip continuation) =
        evaluateHOLFiniteState state continuation := by
    intro state
    rw [hcontinuation, evaluateSkipSeqHOL]
  intro state
  rw [seqAssocHOL.eq_9, evaluateSmartSeqHOL]
  apply evaluateSeqSecondCongr
  intro post
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite,
    evaluateHOLFiniteState_decCall_fixClockRewrite]
  simp only [hc]

end Flapjack
