import Flapjack.HolRef
import Flapjack.Pancake.Semantics.PanProps.EvaluateClockSubAssembly

/-!
# panProps `evaluate_clock_sub1`

Exact counterpart of `panPropsScript.sml:1131-1138` `evaluate_clock_sub1`
(bead `flapjack-4ac.4.60.1`).  HOL derives it from the tagged
`evaluate_add_clock_eq` (`EvaluateAddClockEq.lean`) and the assembled
`evaluate_clock_sub` (`EvaluateClockSubAssembly.lean`): raising the clock of a
non-timeout run by `ck` and subtracting `ck` again cancels.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
open PanSemStateFiniteExact
open PanPropsEvalStateFiniteExact

namespace EvaluateClockSub1Witness
/-- Same-module canonical witness for the `locals`/`globals`/`code`/`eshapes`
    finite-map qualifier of the clock-sub1 theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanPropsEvalStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanPropsEvalStateFiniteExact width σ,
        PanPropsEvalStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanPropsEvalStateFiniteExact.holFmapAsFiniteSupportWitness
end EvaluateClockSub1Witness

/-- PanProps-carrier form of the tagged `evaluate_add_clock_eq`: lift a
    non-`TimeOut` pair run by `ck`.  Untagged support; it is the field-for-field
    codec of `panPropsEvaluateAddClockEq` between `PanPropsEvalStateFiniteExact`
    and `PanSemStateFiniteExact`. -/
private theorem panPropsAddClockPair {width : Nat} {σ : Type} [NeZero width]
    (p : ProgHOL width) (t : PanPropsEvalStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (st : PanPropsEvalStateFiniteExact width σ)
    (ck : Nat) (hRun : evaluateHOLFinitePair t p = (res, st)) (hnt : res ≠ some .timeOut) :
    evaluateHOLFinitePair { t with clock := t.clock + ck } p =
      (res, { st with clock := st.clock + ck }) := by
  have hCan : PanSemStateFiniteExact.evaluateHOLFiniteState t.toPanSemFinite p =
      (res, st.toPanSemFinite) := by
    have e := congrArg (fun q => (q.1, q.2.toPanSemFinite)) hRun
    simpa only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
      PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite] using e
  have hAdd := panPropsEvaluateAddClockEq p t.toPanSemFinite res st.toPanSemFinite ck ⟨hCan, hnt⟩
  have hstate : ({ t with clock := t.clock + ck } : PanPropsEvalStateFiniteExact width σ).toPanSemFinite =
      { t.toPanSemFinite with clock := t.toPanSemFinite.clock + ck } := rfl
  have hgoal : PanSemStateFiniteExact.evaluateHOLFiniteState
      ({ t with clock := t.clock + ck } : PanPropsEvalStateFiniteExact width σ).toPanSemFinite p =
      (res, { st.toPanSemFinite with clock := st.toPanSemFinite.clock + ck }) := by
    rw [hstate]; exact hAdd
  have hpair : evaluateHOLFinitePair { t with clock := t.clock + ck } p =
      (res, PanPropsEvalStateFiniteExact.ofPanSemFinite
        { st.toPanSemFinite with clock := st.toPanSemFinite.clock + ck }) := by
    simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair]
    rw [hgoal]
  rw [hpair]
  congr 1

/-- Exact port of HOL `panProps$evaluate_clock_sub1`
    (`panPropsScript.sml:1131-1138`):

    ```
    !p t res st t' ck.
      evaluate (p,t) = (res,st) /\ res <> SOME TimeOut /\
      evaluate (p,t with clock := ck + t.clock) =
      evaluate (p,t') ==>
      evaluate (p,t) = evaluate (p,t' with clock := t'.clock - ck)
    ```

    over the pair evaluator `evaluateHOLFinitePair`.  The proof is HOL's:
    `evaluate_add_clock_eq` lifts the exact run `(p,t) = (res,st)` to
    `{ t with clock := t.clock + ck }`, which the second hypothesis equates with
    `evaluateHOLFinitePair t' p`; the assembled `evaluate_clock_sub` then
    subtracts `ck` from `t'`. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_clock_sub1"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem panPropsEvaluateClockSub1HOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (p : ProgHOL width) (t : PanPropsEvalStateFiniteExact width σ)
      (res : Option (PanSemResultExact width)) (st : PanPropsEvalStateFiniteExact width σ)
      (t' : PanPropsEvalStateFiniteExact width σ) (ck : Nat),
      evaluateHOLFinitePair t p = (res, st) ∧ res ≠ some .timeOut ∧
      evaluateHOLFinitePair { t with clock := ck + t.clock } p =
        evaluateHOLFinitePair t' p →
      evaluateHOLFinitePair t p =
        evaluateHOLFinitePair { t' with clock := t'.clock - ck } p := by
  intro p t res st t' ck ⟨hRun, hnt, hHigh⟩
  have hAdd := panPropsAddClockPair p t res st ck hRun hnt
  have hHigh' : evaluateHOLFinitePair { t with clock := t.clock + ck } p =
      evaluateHOLFinitePair t' p := by
    have h := hHigh
    rw [Nat.add_comm] at h
    exact h
  have ht' : evaluateHOLFinitePair t' p = (res, { st with clock := st.clock + ck }) := by
    rw [← hHigh', hAdd]
  have hSub := evaluateClockSubHOLFinite p t' res st ck ht' hnt
  rw [hRun, hSub]

end Flapjack
