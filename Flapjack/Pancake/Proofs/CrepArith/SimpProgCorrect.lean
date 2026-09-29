import Flapjack.Pancake.CrepArith
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-!
# Leaf cases of HOL `crep_arith$simp_prog_correct`

The four non-recursive cases below specialize HOL's `simp_prog_correct`
predicate to `Skip`, `Break`, `Continue`, and `Tick`.  Each retains the source
evaluation equation, the `result ≠ SOME Error` side condition, and the target
evaluation conclusion.  The exact carriers are `CrepProgHOL`,
`CrepSemHOLState`, and `CrepResultHOLExact`; the finite-map and word carriers
are qualified on each case theorem.

HOL's `mapcs` is only a local overload in
`crep_arithProofScript.sml:160`, defined as `mapc (λ(key, (params, body)).
(params, simp_prog body))`; `mapc` applies `FMAP_MAP2` to the state's code map
at lines 109-110.  It has no named HOL declaration to tag.  The helper below
is the corresponding exact finite-support state update and remains untagged.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

namespace SimpProgCorrectSupport

/-- Same-module canonical witness for the named finite-map fields on the
    `CrepSemHOLState` carrier used by these HOL-shaped case theorems. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end SimpProgCorrectSupport

/-- Flapjack-only rendering of the proof script's local `mapcs` overload:
    preserve each code key and formal-parameter list, mapping each stored
    program body with the exact HOL-shaped `crepSimpProgHOL`. -/
def crepSimpMapcsHOL {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) : CrepSemHOLState width σ :=
  { state with code := state.code.map2 (fun (_, entry) =>
      (entry.1, crepSimpProgHOL entry.2)) }

/-- Flapjack-only abbreviation (no HOL declaration) of the `simp_prog_correct`
    statement at a fixed program and state, over the shared `mapcs` renderer
    `crepSimpMapcsHOL`: the `evaluate_ind` predicate the case proofs receive for
    a sub-program. -/
def simpProgCorrectAt {width : Nat} [NeZero width] {σ : Type}
    (program : CrepProgHOL width) (state : CrepSemHOLState width σ) : Prop :=
  ∀ (result : Option (CrepResultHOLExact width)) (finalState : CrepSemHOLState width σ),
    evalCrepSemHOLProgExact state program = (result, finalState) →
    result ≠ some .error →
    evalCrepSemHOLProgExact (crepSimpMapcsHOL state) (crepSimpProgHOL program) =
      (result, crepSimpMapcsHOL finalState)

private theorem crepSimpMapcsHOL_emptyLocals {width : Nat} [NeZero width]
    {σ : Type} (state : CrepSemHOLState width σ) :
    crepSimpMapcsHOL (CrepSemHOLState.emptyLocals state) =
      CrepSemHOLState.emptyLocals (crepSimpMapcsHOL state) := by
  cases state
  rfl

private theorem crepSimpMapcsHOL_decClock {width : Nat} [NeZero width]
    {σ : Type} (state : CrepSemHOLState width σ) :
    crepSimpMapcsHOL (decClockCrepSemHOL state) =
      decClockCrepSemHOL (crepSimpMapcsHOL state) := by
  cases state
  rfl

/-- The `Skip` specialization of HOL `simp_prog_correct`
    (`crep_arithProofScript.sml:184-212`). -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_prog_correct"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem simpProgCorrectSkipCase {width : Nat} [NeZero width] {σ : Type} :
    ∀ (state : CrepSemHOLState width σ)
      (result : Option (CrepResultHOLExact width))
      (finalState : CrepSemHOLState width σ),
      evalCrepSemHOLProgExact state (.skip : CrepProgHOL width) =
          (result, finalState) →
      result ≠ some .error →
      evalCrepSemHOLProgExact (crepSimpMapcsHOL state)
          (crepSimpProgHOL (.skip : CrepProgHOL width)) =
        (result, crepSimpMapcsHOL finalState) := by
  intro state result finalState heval _hresult
  rw [evalCrepSemHOLProgExact_skip] at heval
  cases heval
  simp [crepSimpProgHOL, evalCrepSemHOLProgExact_skip]

/-- The `Break` specialization of HOL `simp_prog_correct`
    (`crep_arithProofScript.sml:184-212`). -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_prog_correct"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem simpProgCorrectBreakCase {width : Nat} [NeZero width] {σ : Type} :
    ∀ (state : CrepSemHOLState width σ) (label : Nat)
      (result : Option (CrepResultHOLExact width))
      (finalState : CrepSemHOLState width σ),
      evalCrepSemHOLProgExact state (.break label : CrepProgHOL width) =
          (result, finalState) →
      result ≠ some .error →
      evalCrepSemHOLProgExact (crepSimpMapcsHOL state)
          (crepSimpProgHOL (.break label : CrepProgHOL width)) =
        (result, crepSimpMapcsHOL finalState) := by
  intro state label result finalState heval _hresult
  rw [evalCrepSemHOLProgExact_break] at heval
  cases heval
  simp [crepSimpProgHOL, evalCrepSemHOLProgExact_break]

/-- The `Continue` specialization of HOL `simp_prog_correct`
    (`crep_arithProofScript.sml:184-212`). -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_prog_correct"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem simpProgCorrectContinueCase {width : Nat} [NeZero width] {σ : Type} :
    ∀ (state : CrepSemHOLState width σ) (label : Nat)
      (result : Option (CrepResultHOLExact width))
      (finalState : CrepSemHOLState width σ),
      evalCrepSemHOLProgExact state (.continue label : CrepProgHOL width) =
          (result, finalState) →
      result ≠ some .error →
      evalCrepSemHOLProgExact (crepSimpMapcsHOL state)
          (crepSimpProgHOL (.continue label : CrepProgHOL width)) =
        (result, crepSimpMapcsHOL finalState) := by
  intro state label result finalState heval _hresult
  rw [evalCrepSemHOLProgExact_continue] at heval
  cases heval
  simp [crepSimpProgHOL, evalCrepSemHOLProgExact_continue]

/-- The `Tick` specialization of HOL `simp_prog_correct`
    (`crep_arithProofScript.sml:184-212`).  Its timeout arm clears locals and
    its positive-clock arm decrements the clock, both as in HOL `evaluate_def`.
-/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_prog_correct"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem simpProgCorrectTickCase {width : Nat} [NeZero width] {σ : Type} :
    ∀ (state : CrepSemHOLState width σ)
      (result : Option (CrepResultHOLExact width))
      (finalState : CrepSemHOLState width σ),
      evalCrepSemHOLProgExact state (.tick : CrepProgHOL width) =
          (result, finalState) →
      result ≠ some .error →
      evalCrepSemHOLProgExact (crepSimpMapcsHOL state)
          (crepSimpProgHOL (.tick : CrepProgHOL width)) =
        (result, crepSimpMapcsHOL finalState) := by
  intro state result finalState heval _hresult
  rw [evalCrepSemHOLProgExact_tick] at heval
  by_cases hzero : state.clock = 0
  · rw [if_pos hzero] at heval
    cases heval
    simp only [crepSimpProgHOL]
    rw [evalCrepSemHOLProgExact_tick]
    have hclock : (crepSimpMapcsHOL state).clock = state.clock := rfl
    rw [hclock, if_pos hzero, crepSimpMapcsHOL_emptyLocals]
  · rw [if_neg hzero] at heval
    cases heval
    simp only [crepSimpProgHOL]
    rw [evalCrepSemHOLProgExact_tick]
    have hclock : (crepSimpMapcsHOL state).clock = state.clock := rfl
    rw [hclock, if_neg hzero, ← crepSimpMapcsHOL_decClock]

end Flapjack
