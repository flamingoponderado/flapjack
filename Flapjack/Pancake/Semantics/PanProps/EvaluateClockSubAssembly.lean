import Flapjack.HolRef
import Flapjack.Pancake.Semantics.PanProps.EvaluateClockSubDecCall

/-!
# Assembled HOL `evaluate_clock_sub`

`panPropsScript.sml:724-728` proves

`!p t res st ck. evaluate (p,t) = (res, st with clock := st.clock + ck) /\
  res <> SOME TimeOut ==> evaluate (p, t with clock := t.clock - ck) = (res,st)`

by `recInduct evaluate_ind`.  The assembly applies the tagged `evaluateIndHOL`
(HOL `panSem$evaluate_ind`) to the clock-sub motive `Mc`
(`EvaluateClockSubCall`) and discharges each of its 21 conjuncts with the
tagged constructor case lemmas, translating each HOL IH to the case lemma's
premise through the field-for-field PanProps codec.  No induction hypothesis is
assumed by the public statement. -/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ExpHOL ProgHOL)
open Flapjack.PanSemStateFiniteExact
open Flapjack.PanPropsEvalStateFiniteExact
open Flapjack.EvaluateClockSubCall
open Flapjack.EvaluateClockSubAtoms

namespace EvaluateClockSubAssemblyWitness
/-- Same-module canonical witness for the `locals`/`globals`/`code`/`eshapes`
    finite-map qualifier of the assembled clock-sub theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanPropsEvalStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanPropsEvalStateFiniteExact width σ,
        PanPropsEvalStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanPropsEvalStateFiniteExact.holFmapAsFiniteSupportWitness
end EvaluateClockSubAssemblyWitness

/-- The predicate `P` of HOL's `recInduct evaluate_ind` for `evaluate_clock_sub`,
    over the canonical carrier. -/
private abbrev clockSubIndP {width : Nat} {σ : Type} [NeZero width]
    (pu : ProgHOL width × PanSemStateFiniteExact width σ) : Prop :=
  Mc pu.2 pu.1

private theorem clockSubIndP_all {width : Nat} {σ : Type} [NeZero width] :
    ∀ (p : ProgHOL width) (u : PanSemStateFiniteExact width σ), clockSubIndP (p, u) := by
  classical
  refine evaluateIndHOL (clockSubIndP (width := width) (σ := σ))
    ⟨?skip, ?dec, ?assign, ?prim, ?store, ?store32, ?storeByte, ?shLoad, ?shStore, ?seq, ?ite,
      ?brk, ?cont, ?whl, ?ret, ?rai, ?tick, ?annot, ?call, ?decCall, ?ext⟩
  case skip =>
    exact fun s => mc_of_pair s .skip (evaluateClockSubSkipCaseHOLFinite (ofPanSemFinite s))
  case dec =>
    intro v sh e prog s ih
    refine mc_of_pair s (.dec v sh e prog) ?_
    intro res st ck hRun hnt
    refine evaluateClockSubDecCaseHOLFinite v sh e prog (ofPanSemFinite s) res st ck hRun hnt ?_
    intro value ⟨hev, hshape⟩
    exact pair_of_mc
      (ofPanSemFinite (setVarHOLFinite v value s)) prog
      (by simpa [setVarHOLFinite] using ih value ⟨hev, hshape⟩)
  case assign =>
    exact fun vk v src s =>
      mc_of_pair s (.assign vk v src)
        (evaluateClockSubAssignCaseHOLFinite vk v src (ofPanSemFinite s))
  case prim =>
    exact fun v pop es s =>
      mc_of_pair s (.primitive v pop es)
        (evaluateClockSubPrimitiveCaseHOLFinite v pop es (ofPanSemFinite s))
  case store =>
    exact fun d src s =>
      mc_of_pair s (.store d src) (evaluateClockSubStoreCaseHOLFinite d src (ofPanSemFinite s))
  case store32 =>
    exact fun d src s =>
      mc_of_pair s (.store32 d src)
        (evaluateClockSubStore32CaseHOLFinite d src (ofPanSemFinite s))
  case storeByte =>
    exact fun d src s =>
      mc_of_pair s (.storeByte d src)
        (evaluateClockSubStoreByteCaseHOLFinite d src (ofPanSemFinite s))
  case shLoad =>
    exact fun op vk v ad s =>
      mc_of_pair s (.shMemLoad op vk v ad)
        (evaluateClockSubShMemLoadCaseHOLFinite op vk v ad (ofPanSemFinite s))
  case shStore =>
    exact fun op ad e s =>
      mc_of_pair s (.shMemStore op ad e)
        (evaluateClockSubShMemStoreCaseHOLFinite op ad e (ofPanSemFinite s))
  case seq =>
    intro c1 c2 s ⟨ih2, ih1⟩
    refine mc_of_pair s (.seq c1 c2) ?_
    intro res st ck hRun hnt
    refine evaluateClockSubSeqCaseHOLFinite c1 c2 (ofPanSemFinite s) res st ck hRun hnt ?_ ?_
    · intro firstResult firstState hPair hnone
      have hcanon : (firstResult, firstState.toPanSemFinite) =
          evaluateHOLFiniteState s c1 := by
        have h := congrArg (fun q : Option (PanSemResultExact width) ×
            PanPropsEvalStateFiniteExact width σ => (q.1, q.2.toPanSemFinite)) hPair
        simpa only [evaluateHOLFinitePair, toPanSemFinite_ofPanSemFinite, Prod.eta] using h
      exact pair_of_mc firstState c2
        (ih2 firstResult firstState.toPanSemFinite ⟨hcanon, hnone⟩)
    · exact pair_of_mc (ofPanSemFinite s) c1 (by simpa using ih1)
  case ite =>
    intro e c1 c2 s ih
    refine mc_of_pair s (.ite e c1 c2) ?_
    intro res st ck hRun hnt
    refine evaluateClockSubIfCaseHOLFinite e c1 c2 (ofPanSemFinite s) res st ck hRun hnt ?_
    intro v1 v6 w ⟨he, h2, h3⟩
    exact pair_of_mc (ofPanSemFinite s) (if w ≠ 0 then c1 else c2)
      (ih v1 v6 w ⟨by simpa [toPanSemFinite_ofPanSemFinite] using he, h2, h3⟩)
  case brk =>
    exact fun s => mc_of_pair s .break (evaluateClockSubBreakCaseHOLFinite (ofPanSemFinite s))
  case cont =>
    exact fun s =>
      mc_of_pair s .continue (evaluateClockSubContinueCaseHOLFinite (ofPanSemFinite s))
  case whl =>
    intro e c s ⟨ihc, ihn, ihb⟩
    refine mc_of_pair s (.while e c) ?_
    intro res st ck hRun hnt
    refine evaluateClockSubWhileCaseHOLFinite e c (ofPanSemFinite s) res st ck hRun hnt ?_ ?_ ?_
    · intro v2 v11 word res' s1 v1 ⟨he, h2, h3, hw, hck, hrun, hr, hv1⟩
      have hdecS : ({ ofPanSemFinite s with
          clock := (ofPanSemFinite s).clock - 1 } : PanPropsEvalStateFiniteExact width σ) =
          ofPanSemFinite s.decClockHOLFinite := rfl
      have hcanon : (res', s1.toPanSemFinite) =
          evaluateHOLFiniteState s.decClockHOLFinite c := by
        have h := congrArg (fun q : Option (PanSemResultExact width) ×
            PanPropsEvalStateFiniteExact width σ => (q.1, q.2.toPanSemFinite)) hrun
        simpa only [evaluateHOLFinitePair, hdecS, toPanSemFinite_ofPanSemFinite, Prod.eta] using h
      exact pair_of_mc s1 (.while e c)
        (ihc v2 v11 word res' s1.toPanSemFinite v1
          ⟨by simpa [toPanSemFinite_ofPanSemFinite] using he, h2, h3, hw, hck, hcanon, hr, hv1⟩)
    · intro v2 v11 word res' s1 ⟨he, h2, h3, hw, hck, hrun, hr⟩
      have hdecS : ({ ofPanSemFinite s with
          clock := (ofPanSemFinite s).clock - 1 } : PanPropsEvalStateFiniteExact width σ) =
          ofPanSemFinite s.decClockHOLFinite := rfl
      have hcanon : (res', s1.toPanSemFinite) =
          evaluateHOLFiniteState s.decClockHOLFinite c := by
        have h := congrArg (fun q : Option (PanSemResultExact width) ×
            PanPropsEvalStateFiniteExact width σ => (q.1, q.2.toPanSemFinite)) hrun
        simpa only [evaluateHOLFinitePair, hdecS, toPanSemFinite_ofPanSemFinite, Prod.eta] using h
      exact pair_of_mc s1 (.while e c)
        (ihn v2 v11 word res' s1.toPanSemFinite
          ⟨by simpa [toPanSemFinite_ofPanSemFinite] using he, h2, h3, hw, hck, hcanon, hr⟩)
    · intro v2 v11 word ⟨he, h2, h3, hw, hck⟩
      have hdecS : ({ ofPanSemFinite s with
          clock := (ofPanSemFinite s).clock - 1 } : PanPropsEvalStateFiniteExact width σ) =
          ofPanSemFinite s.decClockHOLFinite := rfl
      refine pair_of_mc ({ ofPanSemFinite s with
        clock := (ofPanSemFinite s).clock - 1 }) c ?_
      rw [hdecS]
      simpa [toPanSemFinite_ofPanSemFinite] using
        ihb v2 v11 word ⟨by simpa [toPanSemFinite_ofPanSemFinite] using he, h2, h3, hw, hck⟩
  case ret =>
    exact fun e s => mc_of_pair s (.return e) (evaluateClockSubReturnCaseHOLFinite e (ofPanSemFinite s))
  case rai =>
    exact fun eid e s =>
      mc_of_pair s (.raise eid e) (evaluateClockSubRaiseCaseHOLFinite eid e (ofPanSemFinite s))
  case tick =>
    exact fun s => mc_of_pair s .tick (evaluateClockSubTickCaseHOLFinite (ofPanSemFinite s))
  case annot =>
    exact fun v0 v1 s =>
      mc_of_pair s (.annot v0 v1) (evaluateClockSubAnnotCaseHOLFinite v0 v1 (ofPanSemFinite s))
  case call =>
    intro caltyp fname argexps s ⟨ihH, ihB⟩
    refine mc_of_pair s (.call caltyp fname argexps) ?_
    intro res st ck hRun hnt
    refine evaluateClockSubCallCaseHOLFinite caltyp fname argexps (ofPanSemFinite s)
      res st ck hRun hnt ?_ ?_
    · intro args v7 prog v12 newlocals return_sh eval_prog v4 st0 v8 eid exn v v1 v2 v3 eid' v5
        evar p sh hargs hlk h7 h12 hck hev1 hev2 hv4 hv8 hct hv hv2 hv3 hv5 heid hsh hexn hvalid
      refine pair_of_mc (ofPanSemFinite (setVarHOLFinite evar exn
        { st0 with locals := (ofPanSemFinite s).toPanSemFinite.locals })) p ?_
      simp only [toPanSemFinite_ofPanSemFinite]
      refine ihH args v7 prog v12 newlocals return_sh eval_prog v4 st0 v8 eid exn v v1 v2 v3 eid'
        v5 evar p sh ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [evalList_eq_mapM]; simpa [toPanSemFinite_ofPanSemFinite] using hargs
      · rw [h7, h12] at hlk ⊢; simpa [toPanSemFinite_ofPanSemFinite] using hlk
      · exact h7
      · exact h12
      · exact hck
      · simpa [PanSemStateFiniteExact.callEntryStateHOLFinite, PanSemStateFiniteExact.decClockHOLFinite, toPanSemFinite_ofPanSemFinite] using hev1
      · exact hev2
      · exact hv4
      · exact hv8
      · exact hct
      · exact hv
      · exact hv2
      · exact hv3
      · exact hv5
      · exact heid
      · exact hsh
      · exact hexn
      · exact hvalid
    · intro args v7 prog v12 newlocals return_sh hargs hlk h7 h12 hck
      refine pair_of_mc (ofPanSemFinite (callEntryStateHOLFinite s newlocals)) prog ?_
      simp only [toPanSemFinite_ofPanSemFinite, PanSemStateFiniteExact.callEntryStateHOLFinite]
      refine ihB args v7 prog v12 newlocals return_sh ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [evalList_eq_mapM]; simpa [toPanSemFinite_ofPanSemFinite] using hargs
      · rw [h7, h12] at hlk ⊢; simpa [toPanSemFinite_ofPanSemFinite] using hlk
      · exact h7
      · exact h12
      · exact hck
  case decCall =>
    intro rt shape fname argexps prog1 s ⟨ihC, ihB⟩
    refine mc_of_pair s (.decCall rt shape fname argexps prog1) ?_
    intro res st ck hRun hnt
    refine evaluateClockSubDecCallCaseHOLFinite rt shape fname argexps prog1 (ofPanSemFinite s)
      res st ck hRun hnt ?_ ?_
    · intro args v2 prog v7 newlocals return_sh eval_prog v st0 v3 retv
        hargs hlk h2 h7 hck hev1 hev2 hv hv3 hs1 hs2
      refine pair_of_mc (ofPanSemFinite (setVarHOLFinite rt retv
        { st0 with locals := (ofPanSemFinite s).toPanSemFinite.locals })) prog1 ?_
      simp only [toPanSemFinite_ofPanSemFinite]
      refine ihC args v2 prog v7 newlocals return_sh eval_prog v st0 v3 retv
        ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [evalList_eq_mapM]; simpa [toPanSemFinite_ofPanSemFinite] using hargs
      · rw [h2, h7] at hlk ⊢; simpa [toPanSemFinite_ofPanSemFinite] using hlk
      · exact h2
      · exact h7
      · exact hck
      · simpa [PanSemStateFiniteExact.callEntryStateHOLFinite, PanSemStateFiniteExact.decClockHOLFinite, toPanSemFinite_ofPanSemFinite] using hev1
      · exact hev2
      · exact hv
      · exact hv3
      · exact hs1
      · exact hs2
    · intro args v2 prog v7 newlocals return_sh hargs hlk h2 h7 hck
      refine pair_of_mc (ofPanSemFinite (callEntryStateHOLFinite s newlocals)) prog ?_
      simp only [toPanSemFinite_ofPanSemFinite, PanSemStateFiniteExact.callEntryStateHOLFinite]
      refine ihB args v2 prog v7 newlocals return_sh ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [evalList_eq_mapM]; simpa [toPanSemFinite_ofPanSemFinite] using hargs
      · rw [h2, h7] at hlk ⊢; simpa [toPanSemFinite_ofPanSemFinite] using hlk
      · exact h2
      · exact h7
      · exact hck
  case ext =>
    exact fun f a b c d s =>
      mc_of_pair s (.extCall f a b c d)
        (evaluateClockSubExtCallCaseHOLFinite f a b c d (ofPanSemFinite s))

/-- Exact port of HOL `panProps$evaluate_clock_sub` (`panPropsScript.sml:724-728`):
    `∀p t res st ck. evaluate (p,t) = (res, st with clock := st.clock + ck) ∧
    res ≠ SOME TimeOut ⇒ evaluate (p, t with clock := t.clock - ck) = (res,st)`,
    over the pair evaluator `evaluateHOLFinitePair`.  The proof is HOL's
    `recInduct evaluate_ind`, with each conjunct discharged by the tagged
    constructor case lemma; no induction hypothesis is assumed. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_clock_sub" 724
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateClockSubHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (p : ProgHOL width) (t : PanPropsEvalStateFiniteExact width σ)
      (res : Option (PanSemResultExact width)) (st : PanPropsEvalStateFiniteExact width σ)
      (ck : Nat),
      evaluateHOLFinitePair t p = (res, { st with clock := st.clock + ck }) →
      res ≠ some .timeOut →
      evaluateHOLFinitePair { t with clock := t.clock - ck } p = (res, st) := by
  intro p t res st ck hRun hnt
  exact pair_of_mc t p (clockSubIndP_all p t.toPanSemFinite) res st ck hRun hnt

end Flapjack
