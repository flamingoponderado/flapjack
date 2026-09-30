import Flapjack.Pancake.Semantics.PanSem.AddClock
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
import Flapjack.Pancake.Semantics.PanSem.EvaluateFinite

/-!
# HOL `evaluate_add_clock_or_timeout` over the exact finite-map PanSem evaluator

`evaluateHOLFiniteState_add_clock_or_timeout` ports HOL
`cakeml/pancake/semantics/panPropsScript.sml:834-857` over the finite-map
evaluator `evaluateHOLFiniteState`. The exact line-780 `evaluate_def` equation
theorem establishes that this evaluator has HOL's 21 constructor clauses.

The statement is HOL's: if the run at the input state `s` fixes its result
clock to `0` and is not a timeout, then running the same program at any other
clock `k` either times out (only when `k` is smaller than `s.clock`) or returns
the same result with the clock shifted by `k - s.clock`.

The proof lifts both finite runs to the broad exact evaluator
`evalPanSemRecursiveCallContextHOLExact` through the kernel-checked projection
`evalPanSemRecursiveCallFiniteContext_projection`, then applies the
Flapjack-specific clock-shift lemma `eval_add_clock_mono_aux`.
-/

open Flapjack.Pancake.PanLang (ProgHOL)
open Flapjack.PanSemStateFiniteExact

namespace Flapjack

/-- `toExact` is injective on the finite-support carrier: the canonical
    finite-map fields are determined by their lookup functions and the
    finite-support proofs are propositionally irrelevant. -/
theorem PanSemStateFiniteExact.toExact_injective {width : Nat} {σ : Type} [NeZero width]
    {a b : PanSemStateFiniteExact width σ} (h : a.toExact = b.toExact) : a = b := by
  cases a with
  | mk al ag ast ac ae amm amem asm aclk abe affi aba ata =>
    cases b with
    | mk bl bg bst bc be bmm bmem bsm bclk bbe bffi bba bta =>
      simp only [PanSemStateFiniteExact.toExact] at h
      injection h with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
      have e1 : al = bl := HolFiniteMapExact.ext h1
      have e2 : ag = bg := HolFiniteMapExact.ext h2
      have e4 : ac = bc := HolFiniteMapExact.ext h4
      have e5 : ae = be := HolFiniteMapExact.ext h5
      rw [e1, e2, h3, e4, e5, h6, h7, h8, h9, h10, h11, h12, h13]

/- Same-module canonical witness required by the finite-support qualifier on
   `evaluateHOLFiniteState_add_clock_or_timeout`. It re-exports the checked
   `toExact`/`ofExact` roundtrip for the owning `PanSemStateFiniteExact`
   carrier and its broad counterpart. -/
namespace PanSem.ClockTimeoutWitness

theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

end PanSem.ClockTimeoutWitness

/-- Source-reviewed against HOL `panPropsScript.sml:834-857`. The theorem keeps
    the HOL premise order and exact alternatives: the base run returns `q` at
    `t` with clock zero and is non-timeout; an arbitrary-clock run either times
    out below the input clock or returns `q` at `t` with the clock shifted by
    `k - s.clock`. The evaluator is `evaluateHOLFiniteState`, whose exact
    21-clause equation port is `evaluateHOLFiniteState_eq_evaluate_def` at
    `panSemScript.sml:780`. The four `HolFiniteMapExact` state fields are
    recorded by `fmap_as_finite_support`; the positive width-indexed word
    carrier is recorded by `words_as_type_indexed_bitvec`. The clock-shift
    helper and finite-to-broad projection are Flapjack-specific proof
    infrastructure and add no premise to this statement. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_add_clock_or_timeout" 834
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateHOLFiniteState_add_clock_or_timeout {width : Nat} {σ : Type} [NeZero width]
    (p : ProgHOL width) (s : PanSemStateFiniteExact width σ)
    (q : Option (PanSemResultExact width)) (t : PanSemStateFiniteExact width σ)
    (h0 : evaluateHOLFiniteState s p = (q, { t with clock := 0 }))
    (hnt : q ≠ some .timeOut)
    (k : Nat) (q' : Option (PanSemResultExact width)) (t' : PanSemStateFiniteExact width σ)
    (hk : evaluateHOLFiniteState { s with clock := k } p = (q', t')) :
    (q' = some .timeOut ∧ k < s.clock) ∨
      (q' = q ∧ s.clock ≤ k ∧ t' = { t with clock := k - s.clock }) := by
  classical
  let hm : DecidablePred s.memaddrs := fun a => Classical.propDecidable (s.memaddrs a)
  let hs : DecidablePred s.shMemaddrs := fun a => Classical.propDecidable (s.shMemaddrs a)
  let fcS : FiniteEvalContext width σ := ⟨s, hm, hs⟩
  let fcK : FiniteEvalContext width σ := ⟨{ s with clock := k }, hm, hs⟩
  obtain ⟨out, hrecS⟩ := evalPanSemRecursiveCallFiniteContext_total p fcS
  obtain ⟨outK, hrecK⟩ := evalPanSemRecursiveCallFiniteContext_total p fcK
  have h0w : evaluateHOLFiniteStateWithDeciders s p (h := hm) (hshared := hs) =
      (q, { t with clock := 0 }) := by
    rw [← evaluateHOLFiniteState_eq_withDeciders (state := s) (hmem := hm) (hshared := hs)
      (program := p)]
    exact h0
  simp only [evaluateHOLFiniteStateWithDeciders, fcS, hrecS] at h0w
  have hkw : evaluateHOLFiniteStateWithDeciders { s with clock := k } p
      (h := hm) (hshared := hs) = (q', t') := by
    rw [← evaluateHOLFiniteState_eq_withDeciders (state := { s with clock := k })
      (hmem := hm) (hshared := hs) (program := p)]
    exact hk
  simp only [evaluateHOLFiniteStateWithDeciders, fcK, hrecK] at hkw
  have hout1 : out.1 = q := congrArg Prod.fst h0w
  have hout2 : out.2.state = { t with clock := 0 } := congrArg Prod.snd h0w
  have houtK1 : outK.1 = q' := congrArg Prod.fst hkw
  have houtK2 : outK.2.state = t' := congrArg Prod.snd hkw
  have hLow : evalPanSemRecursiveCallContextHOLExact p fcS.toExact =
      some (out.1, out.2.toExact) := by
    have hproj := evalPanSemRecursiveCallFiniteContext_projection p fcS
    simp only [hrecS, Option.map_some] at hproj
    exact hproj.symm
  have hHighK : evalPanSemRecursiveCallContextHOLExact p fcK.toExact =
      some (outK.1, outK.2.toExact) := by
    have hproj := evalPanSemRecursiveCallFiniteContext_projection p fcK
    simp only [hrecK, Option.map_some] at hproj
    exact hproj.symm
  have hstate1 : outK.2.toExact.state = t'.toExact := by
    change outK.2.state.toExact = t'.toExact
    rw [houtK2]
  have hstate2 : out.2.toExact.state =
      ({ t with clock := 0 } : PanSemStateFiniteExact width σ).toExact := by
    change out.2.state.toExact = _
    rw [hout2]
  by_cases hle : s.clock ≤ k
  · right
    have hstateA : (ctxAddClock fcS.toExact (k - s.clock)).state = fcK.toExact.state := by
      change stateAddClock s.toExact (k - s.clock) =
        ({ s with clock := k } : PanSemStateFiniteExact width σ).toExact
      rw [show stateAddClock s.toExact (k - s.clock) =
          { s.toExact with clock := s.clock + (k - s.clock) } from rfl]
      rw [show s.clock + (k - s.clock) = k from by omega]
    have hHighA : evalPanSemRecursiveCallContextHOLExact p
        (ctxAddClock fcS.toExact (k - s.clock)) = some (outK.1, outK.2.toExact) :=
      (eval_context_state p (ctxAddClock fcS.toExact (k - s.clock)) fcK.toExact hstateA).trans
        hHighK
    have hmono := eval_add_clock_mono_aux p fcS.toExact (k - s.clock)
      (out.1, out.2.toExact) (outK.1, outK.2.toExact) hLow hHighA
    have hne : (out.1, out.2.toExact).1 ≠ some .timeOut := by
      rw [hout1]
      exact hnt
    have hres := hmono.2 hne
    have hres1 : outK.1 = out.1 := (Prod.mk.inj hres).1
    have hres2 : outK.2.toExact = ctxAddClock out.2.toExact (k - s.clock) := (Prod.mk.inj hres).2
    refine ⟨?_, hle, ?_⟩
    · rw [← houtK1, hres1, hout1]
    · have hEq : t'.toExact =
          stateAddClock ({ t with clock := 0 } : PanSemStateFiniteExact width σ).toExact
            (k - s.clock) := by
        rw [← hstate1]
        have h := congrArg PanSemExactEvalContext.state hres2
        change outK.2.toExact.state = stateAddClock out.2.toExact.state (k - s.clock) at h
        rw [hstate2] at h
        exact h
      have hEq2 : t'.toExact =
          ({ t with clock := k - s.clock } : PanSemStateFiniteExact width σ).toExact := by
        rw [hEq]
        rw [show stateAddClock ({ t with clock := 0 } : PanSemStateFiniteExact width σ).toExact
              (k - s.clock) =
            ({ { t with clock := 0 } with clock :=
                ({ t with clock := 0 } : PanSemStateFiniteExact width σ).toExact.clock +
                  (k - s.clock) } : PanSemStateFiniteExact width σ).toExact from rfl]
        rw [show ({ t with clock := 0 } : PanSemStateFiniteExact width σ).toExact.clock = 0
            from rfl]
        rw [Nat.zero_add]
      exact PanSemStateFiniteExact.toExact_injective hEq2
  · left
    have hklt : k < s.clock := by omega
    by_cases hq' : q' = some .timeOut
    · exact ⟨hq', hklt⟩
    · exfalso
      have hstateB : (ctxAddClock fcK.toExact (s.clock - k)).state = fcS.toExact.state := by
        change stateAddClock ({ s with clock := k } : PanSemStateFiniteExact width σ).toExact
            (s.clock - k) = s.toExact
        rw [show stateAddClock ({ s with clock := k } : PanSemStateFiniteExact width σ).toExact
              (s.clock - k) =
            { ({ s with clock := k } : PanSemStateFiniteExact width σ).toExact with
              clock := ({ s with clock := k } :
                PanSemStateFiniteExact width σ).toExact.clock + (s.clock - k) } from rfl]
        rw [show ({ s with clock := k } : PanSemStateFiniteExact width σ).toExact.clock = k
            from rfl]
        rw [show k + (s.clock - k) = s.clock from by omega]
      have hHighB : evalPanSemRecursiveCallContextHOLExact p
          (ctxAddClock fcK.toExact (s.clock - k)) = some (out.1, out.2.toExact) :=
        (eval_context_state p (ctxAddClock fcK.toExact (s.clock - k)) fcS.toExact hstateB).trans
          hLow
      have hmono := eval_add_clock_mono_aux p fcK.toExact (s.clock - k)
        (outK.1, outK.2.toExact) (out.1, out.2.toExact) hHighK hHighB
      have hne : (outK.1, outK.2.toExact).1 ≠ some .timeOut := by
        rw [houtK1]
        exact hq'
      have hres := hmono.2 hne
      have hres2 : out.2.toExact = ctxAddClock outK.2.toExact (s.clock - k) :=
        (Prod.mk.inj hres).2
      have hmem : out.2.toExact.state.clock = 0 := by
        change out.2.state.toExact.clock = 0
        rw [hout2]
      have hz : s.clock - k = 0 := by
        have h : out.2.toExact.state.clock =
            outK.2.toExact.state.clock + (s.clock - k) :=
          congrArg PanSemStateExact.clock (congrArg PanSemExactEvalContext.state hres2)
        have h0 : outK.2.toExact.state.clock + (s.clock - k) = 0 := by rw [← h, hmem]
        exact (Nat.add_eq_zero_iff.mp h0).2
      omega

/-! ## Clock-increase FFI-event prefix

At a larger clock, evaluation can only append FFI I/O events. The state-level
projection helper below is Flapjack-specific finite-to-broad infrastructure.
The HOL-shaped theorem is placed in the panProps counterpart submodule
`PanProps/EvaluateAddClockIoEventsMono.lean`. -/

/-- Flapjack-specific bridge: a successful finite-context run projects to the
    broad exact evaluator applied to `toExact`, so the FFI event trace of the
    finite post-state is the broad run's trace. -/
private theorem evalPanSemRecursiveCallContextHOLExact_map_toExact_some
    {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) (context : FiniteEvalContext width σ)
    (pair : Option (PanSemResultExact width) × FiniteEvalContext width σ)
    (h : evalPanSemRecursiveCallFiniteContext program context = some pair) :
    evalPanSemRecursiveCallContextHOLExact program context.toExact =
      some (pair.1, pair.2.toExact) := by
  have hproj := evalPanSemRecursiveCallFiniteContext_projection program context
  rw [h] at hproj
  simpa using hproj.symm

/-- Flapjack-specific state-level projection helper for clock-increase FFI
    prefixes. The two `DecidablePred` witnesses are supplied internally by
    `evaluateHOLFiniteState`'s classical choice; totality discharges both outer
    assembly markers. The HOL theorem with its original binder order lives
    in the panProps counterpart. -/
theorem evaluateHOLFiniteState_add_clock_ioEvents_prefix {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ) (program : ProgHOL width)
    (extra : Nat) :
    (evaluateHOLFiniteState state program).2.ffi.ioEvents <+:
      (evaluateHOLFiniteState { state with clock := state.clock + extra } program).2.ffi.ioEvents := by
  classical
  let s1 : PanSemStateFiniteExact width σ := { state with clock := state.clock + extra }
  let c0 : FiniteEvalContext width σ :=
    ⟨state, fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩
  let c1 : FiniteEvalContext width σ :=
    ⟨s1, fun address => Classical.propDecidable (s1.memaddrs address),
      fun address => Classical.propDecidable (s1.shMemaddrs address)⟩
  obtain ⟨pair0, hpair0⟩ := evalPanSemRecursiveCallFiniteContext_total program c0
  obtain ⟨pair1, hpair1⟩ := evalPanSemRecursiveCallFiniteContext_total program c1
  have hev0 : evaluateHOLFiniteState state program = (pair0.1, pair0.2.state) :=
    evaluateHOLFiniteState_eq_of_recursiveContext state program c0 rfl pair0 hpair0
  have hev1 : evaluateHOLFiniteState s1 program = (pair1.1, pair1.2.state) :=
    evaluateHOLFiniteState_eq_of_recursiveContext s1 program c1 rfl pair1 hpair1
  have hctx1 : c1.toExact = ctxAddClock c0.toExact extra := by
    apply PanSemExactEvalContext.ext
    rfl
  have hproj0 := evalPanSemRecursiveCallContextHOLExact_map_toExact_some program c0 pair0 hpair0
  have hproj1 := evalPanSemRecursiveCallContextHOLExact_map_toExact_some program c1 pair1 hpair1
  have hpre := evalPanSemRecursiveCallContextHOLExact_add_clock_ioEvents_prefix_getD
    program c0.toExact extra
  rw [hproj0, ← hctx1, hproj1] at hpre
  rw [hev0, hev1]
  simpa [FiniteEvalContext.toExact, PanSemStateFiniteExact.toExact] using hpre

end Flapjack
