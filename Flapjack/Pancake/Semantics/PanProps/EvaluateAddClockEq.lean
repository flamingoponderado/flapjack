import Flapjack.Pancake.Semantics.PanSem.ClockTimeout

/-! Exact counterpart of `panPropsScript.sml:698-701` `evaluate_add_clock_eq`
(bead `flapjack-pxn.18.4.4.3`). -/

namespace Flapjack

open Flapjack.Pancake.PanLang (ProgHOL)
open PanSemStateFiniteExact

namespace PanPropsAddClockEqSupport

/-- Canonical finite-support roundtrip for the four state map fields. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

end PanPropsAddClockEqSupport

/-- Exact HOL `evaluate_add_clock_eq` (`panPropsScript.sml:698-701`):

    ```
    !p t res st ck.
      evaluate (p,t) = (res,st) /\ res <> SOME TimeOut ==>
      evaluate (p,t with clock := t.clock + ck) = (res,st with clock := st.clock + ck)
    ```

    Both runs use the finite evaluator whose constructor equations are
    tagged against the rebound `panSem$evaluate_def` at line 780.  The proof
    lifts the broad clock-shift lemma `eval_add_clock_mono_aux` through the
    kernel-checked finite-to-broad projection, as the tagged
    `evaluate_add_clock_io_events_mono` does. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_add_clock_eq"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem panPropsEvaluateAddClockEq {width : Nat} {σ : Type} [NeZero width] :
    ∀ (p : ProgHOL width) (t : PanSemStateFiniteExact width σ)
      (res : Option (PanSemResultExact width)) (st : PanSemStateFiniteExact width σ) (ck : Nat),
      evaluateHOLFiniteState t p = (res, st) ∧ res ≠ some .timeOut →
      evaluateHOLFiniteState { t with clock := t.clock + ck } p =
        (res, { st with clock := st.clock + ck }) := by
  classical
  intro p t res st ck ⟨hev, hnt⟩
  let s1 : PanSemStateFiniteExact width σ := { t with clock := t.clock + ck }
  let c0 : FiniteEvalContext width σ :=
    ⟨t, fun address => Classical.propDecidable (t.memaddrs address),
      fun address => Classical.propDecidable (t.shMemaddrs address)⟩
  let c1 : FiniteEvalContext width σ :=
    ⟨s1, fun address => Classical.propDecidable (s1.memaddrs address),
      fun address => Classical.propDecidable (s1.shMemaddrs address)⟩
  obtain ⟨pair0, hpair0⟩ := evalPanSemRecursiveCallFiniteContext_total p c0
  obtain ⟨pair1, hpair1⟩ := evalPanSemRecursiveCallFiniteContext_total p c1
  have hev0 : evaluateHOLFiniteState t p = (pair0.1, pair0.2.state) :=
    evaluateHOLFiniteState_eq_of_recursiveContext t p c0 rfl pair0 hpair0
  have hev1 : evaluateHOLFiniteState s1 p = (pair1.1, pair1.2.state) :=
    evaluateHOLFiniteState_eq_of_recursiveContext s1 p c1 rfl pair1 hpair1
  have hctx1 : c1.toExact = ctxAddClock c0.toExact ck := by
    apply PanSemExactEvalContext.ext
    rfl
  have hproj0 : evalPanSemRecursiveCallContextHOLExact p c0.toExact =
      some (pair0.1, pair0.2.toExact) := by
    have h := evalPanSemRecursiveCallFiniteContext_projection p c0
    rw [hpair0] at h
    simpa using h.symm
  have hproj1 : evalPanSemRecursiveCallContextHOLExact p (ctxAddClock c0.toExact ck) =
      some (pair1.1, pair1.2.toExact) := by
    have h := evalPanSemRecursiveCallFiniteContext_projection p c1
    rw [hpair1, hctx1] at h
    simpa using h.symm
  rw [hev0] at hev
  obtain ⟨hres, hst⟩ := Prod.mk.inj hev
  have key := (eval_add_clock_mono_aux p c0.toExact ck _ _ hproj0 hproj1).2
    (by rw [hres]; exact hnt)
  obtain ⟨hr1, hc1⟩ := Prod.mk.inj key
  show evaluateHOLFiniteState s1 p = _
  rw [hev1, hr1, hres]
  congr 1
  apply PanSemStateFiniteExact.toExact_injective
  have := congrArg PanSemExactEvalContext.state hc1
  rw [← hst]
  simpa [FiniteEvalContext.toExact, ctxAddClock, PanSemStateFiniteExact.toExact] using this

end Flapjack
