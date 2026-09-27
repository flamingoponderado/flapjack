import Flapjack.Pancake.Semantics.PanSem.FiniteSupportStep
import Flapjack.Pancake.Semantics.PanSem.StateSimpExact

/-!
# Clock-shift infrastructure for the exact `panSem` evaluator

FLAPJACK-SPECIFIC (untagged) infrastructure towards HOL
`panPropsScript.sml:881` `evaluate_add_clock_io_events_mono` / the underlying
`evaluate_add_clock_eq` (bead `flapjack-dpvn`, prerequisite of `flapjack-tu4j`).

This module provides the clock-shift helpers `stateAddClock` / `ctxAddClock`
with their projection lemmas, the commutation of the exact state updates
(`setVarHOLExact`, `setGlobalHOLExact`, `setKvarHOLExact`, `emptyLocalsHOLExact`,
`decClockHOLExact`, `fixClockHOLExact`, `evalHOLExact`, `evalListHOLExact`,
`isValidValueHOLExact`) with the clock shift, and the bridge `eval_context_state`
(`eval c1 = eval c2` when `c1.state = c2.state`), which sidesteps the generated
`DecidablePred` proof terms of `withState`.

The full result-agreement lemma is still open and tracked by `flapjack-dpvn`.
No declaration here carries an `@[hol]` tag.
-/

open Flapjack.Pancake.PanLang (MlS ExpHOL ProgHOL ShapeHOL)

namespace Flapjack

/-! ## Clock-shift helper infrastructure -/

abbrev stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (extra : Nat) : PanSemStateExact width σ :=
  { state with clock := state.clock + extra }

abbrev ctxAddClock {width : Nat} {σ : Type} [NeZero width]
    (context : PanSemExactEvalContext width σ) (extra : Nat) : PanSemExactEvalContext width σ :=
  { context with state := stateAddClock context.state extra }

@[simp] theorem stateAddClock_clock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (extra : Nat) :
    (stateAddClock state extra).clock = state.clock + extra := rfl

@[simp] theorem stateAddClock_locals {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (extra : Nat) :
    (stateAddClock state extra).locals = state.locals := rfl

@[simp] theorem stateAddClock_globals {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (extra : Nat) :
    (stateAddClock state extra).globals = state.globals := rfl

@[simp] theorem stateAddClock_structs {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (extra : Nat) :
    (stateAddClock state extra).structs = state.structs := rfl

@[simp] theorem stateAddClock_code {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (extra : Nat) :
    (stateAddClock state extra).code = state.code := rfl

@[simp] theorem stateAddClock_eshapes {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (extra : Nat) :
    (stateAddClock state extra).eshapes = state.eshapes := rfl

@[simp] theorem stateAddClock_memory {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (extra : Nat) :
    (stateAddClock state extra).memory = state.memory := rfl

@[simp] theorem stateAddClock_memaddrs {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (extra : Nat) :
    (stateAddClock state extra).memaddrs = state.memaddrs := rfl

@[simp] theorem stateAddClock_shMemaddrs {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (extra : Nat) :
    (stateAddClock state extra).shMemaddrs = state.shMemaddrs := rfl

@[simp] theorem stateAddClock_be {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (extra : Nat) :
    (stateAddClock state extra).be = state.be := rfl

@[simp] theorem stateAddClock_ffi {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (extra : Nat) :
    (stateAddClock state extra).ffi = state.ffi := rfl

@[simp] theorem stateAddClock_baseAddr {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (extra : Nat) :
    (stateAddClock state extra).baseAddr = state.baseAddr := rfl

@[simp] theorem stateAddClock_topAddr {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (extra : Nat) :
    (stateAddClock state extra).topAddr = state.topAddr := rfl

@[simp] theorem ctxAddClock_state {width : Nat} {σ : Type} [NeZero width]
    (context : PanSemExactEvalContext width σ) (extra : Nat) :
    (ctxAddClock context extra).state = stateAddClock context.state extra := rfl

@[simp] theorem stateAddClock_zero {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) : stateAddClock state 0 = state := by
  simp only [stateAddClock, Nat.add_zero]

theorem stateAddClock_memaddrsDecidable {width : Nat} {σ : Type} [NeZero width]
    (context : PanSemExactEvalContext width σ) (extra : Nat) :
    (ctxAddClock context extra).memaddrsDecidable = context.memaddrsDecidable := rfl

theorem stateAddClock_shMemaddrsDecidable {width : Nat} {σ : Type} [NeZero width]
    (context : PanSemExactEvalContext width σ) (extra : Nat) :
    (ctxAddClock context extra).shMemaddrsDecidable = context.shMemaddrsDecidable := rfl

@[simp] theorem ctxAddClock_withState {width : Nat} {σ : Type} [NeZero width]
    (context : PanSemExactEvalContext width σ) (state : PanSemStateExact width σ)
    (hmem : state.memaddrs = context.state.memaddrs)
    (hshared : state.shMemaddrs = context.state.shMemaddrs) (extra : Nat) :
    ctxAddClock (context.withState state hmem hshared) extra =
      (ctxAddClock context extra).withState (stateAddClock state extra)
        (by rw [stateAddClock_memaddrs]; exact hmem)
        (by rw [stateAddClock_shMemaddrs]; exact hshared) :=
  PanSemExactEvalContext.ext rfl

@[simp] theorem setVarHOLExact_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (state : PanSemStateExact width σ) (extra : Nat) :
    setVarHOLExact name value (stateAddClock state extra) =
      stateAddClock (setVarHOLExact name value state) extra := rfl

@[simp] theorem setGlobalHOLExact_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (state : PanSemStateExact width σ) (extra : Nat) :
    setGlobalHOLExact name value (stateAddClock state extra) =
      stateAddClock (setGlobalHOLExact name value state) extra := rfl

@[simp] theorem setKvarHOLExact_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (kind : VarKind) (name : MlS) (value : ValueHOL width)
    (state : PanSemStateExact width σ) (extra : Nat) :
    setKvarHOLExact kind name value (stateAddClock state extra) =
      stateAddClock (setKvarHOLExact kind name value state) extra := by
  cases kind <;> rfl

@[simp] theorem emptyLocalsHOLExact_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (extra : Nat) :
    emptyLocalsHOLExact (stateAddClock state extra) =
      stateAddClock (emptyLocalsHOLExact state) extra := rfl

theorem decClockHOLExact_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (extra : Nat) (h : state.clock ≠ 0) :
    decClockHOLExact (stateAddClock state extra) =
      stateAddClock (decClockHOLExact state) extra := by
  simp only [decClockHOLExact, stateAddClock]
  rw [show state.clock + extra - 1 = state.clock - 1 + extra by omega]

theorem fixClockHOLExact_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    {β : Type} (oldState : PanSemStateExact width σ)
    (step : β × PanSemStateExact width σ) (extra : Nat) :
    fixClockHOLExact (stateAddClock oldState extra)
        (step.1, stateAddClock step.2 extra) =
      (step.1, stateAddClock (fixClockHOLExact oldState step).2 extra) := by
  obtain ⟨res, st⟩ := step
  simp only [fixClockHOLExact, stateAddClock]
  congr 1
  by_cases h : oldState.clock < st.clock
  · simp [h, Nat.add_lt_add_iff_right]
  · simp [h, Nat.add_lt_add_iff_right]

theorem fixClockHOLExact_stateAddClock_pair {width : Nat} {σ : Type} [NeZero width]
    {β : Type} (oldState : PanSemStateExact width σ) (res : β)
    (st : PanSemStateExact width σ) (extra : Nat) :
    fixClockHOLExact (stateAddClock oldState extra) (res, stateAddClock st extra) =
      (res, stateAddClock (fixClockHOLExact oldState (res, st)).2 extra) :=
  fixClockHOLExact_stateAddClock oldState (res, st) extra

theorem ctxAddClock_withState_fixClock {width : Nat} {σ : Type} [NeZero width]
    (outer : PanSemExactEvalContext width σ) (oldState : PanSemStateExact width σ)
    (res : Option (PanSemResultExact width)) (extra : Nat)
    {hm' : (fixClockHOLExact (stateAddClock oldState extra)
        (res, stateAddClock outer.state extra)).2.memaddrs =
      (ctxAddClock outer extra).state.memaddrs}
    {hs' : (fixClockHOLExact (stateAddClock oldState extra)
        (res, stateAddClock outer.state extra)).2.shMemaddrs =
      (ctxAddClock outer extra).state.shMemaddrs} :
    (ctxAddClock outer extra).withState
        (fixClockHOLExact (stateAddClock oldState extra)
          (res, stateAddClock outer.state extra)).2 hm' hs' =
      ctxAddClock (outer.withState (fixClockHOLExact oldState (res, outer.state)).2
        rfl rfl) extra := by
  apply PanSemExactEvalContext.ext
  exact congrArg Prod.snd (fixClockHOLExact_stateAddClock_pair oldState res outer.state extra)

theorem callEntryStateHOLExact_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ)
    (calleeLocals : MlS → Option (ValueHOL width)) (extra : Nat) (h : state.clock ≠ 0) :
    callEntryStateHOLExact (stateAddClock state extra) calleeLocals =
      stateAddClock (callEntryStateHOLExact state calleeLocals) extra := by
  simp only [callEntryStateHOLExact, stateAddClock]
  rw [show state.clock + extra - 1 = state.clock - 1 + extra by omega]

@[simp] theorem evalHOLExact_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (expression : ExpHOL width) (extra : Nat) :
    evalHOLExact (stateAddClock state extra) expression = evalHOLExact state expression := by
  unfold stateAddClock
  exact evalHOLExact_upd_clock_eq state expression (state.clock + extra)

@[simp] theorem evalListHOLExact_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (expressions : List (ExpHOL width)) (extra : Nat) :
    evalListHOLExact (stateAddClock state extra) expressions =
      evalListHOLExact state expressions := by
  induction expressions with
  | nil => simp only [evalListHOLExact]
  | cons head tail ih =>
      simp only [evalListHOLExact, evalHOLExact_stateAddClock, ih]

@[simp] theorem isValidValueHOLExact_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (kind : VarKind) (name : MlS)
    (value : ValueHOL width) (extra : Nat) :
    isValidValueHOLExact (stateAddClock state extra) kind name value =
      isValidValueHOLExact state kind name value := by
  unfold stateAddClock
  exact (is_valid_value_simps2 state kind name value (state.clock + extra)
    state.ffi state.code state.memory).1

theorem ctxAddClock_withState_inv {width : Nat} {σ : Type} [NeZero width]
    (context : PanSemExactEvalContext width σ) (state : PanSemStateExact width σ)
    (hmem : state.memaddrs = context.state.memaddrs)
    (hshared : state.shMemaddrs = context.state.shMemaddrs) (extra : Nat) :
    (ctxAddClock context extra).withState (stateAddClock state extra)
        (by rw [stateAddClock_memaddrs]; exact hmem)
        (by rw [stateAddClock_shMemaddrs]; exact hshared) =
      ctxAddClock (context.withState state hmem hshared) extra :=
  (ctxAddClock_withState context state hmem hshared extra).symm

theorem ctxAddClock_withState_generic {width : Nat} {σ : Type} [NeZero width]
    (context : PanSemExactEvalContext width σ) (state : PanSemStateExact width σ) (extra : Nat)
    (hm : state.memaddrs = context.state.memaddrs)
    (hs : state.shMemaddrs = context.state.shMemaddrs)
    (hm' : (stateAddClock state extra).memaddrs = (ctxAddClock context extra).state.memaddrs)
    (hs' : (stateAddClock state extra).shMemaddrs = (ctxAddClock context extra).state.shMemaddrs) :
    (ctxAddClock context extra).withState (stateAddClock state extra) hm' hs' =
      ctxAddClock (context.withState state hm hs) extra := by
  apply PanSemExactEvalContext.ext
  rfl

/-! ## Blocker (bead flapjack-dpvn)

The clock-shift helper infrastructure above compiles, but the full
result-agreement lemma `evalPanSemRecursiveCallContextHOLExact`
add-clock equality is blocked on rewriting the `withState`-built
evaluation contexts.  The equation compiler generates opaque proof
terms for the `DecidablePred` fields of `PanSemExactEvalContext`,
e.g. `evalPanSemRecursiveCallContextHOLExact._proof_5 (ctxAddClock
context extra) ...`; these are propositionally equal to the simple
`rfl` proofs used by the helper lemmas, but `rw`/`simp` cannot match
them under the implicit transparency level, so the longer run's
recursive call cannot be rewritten to `eval sub (ctxAddClock subCtx
extra)` to apply the induction hypothesis.

A robust fix is a prior lemma that `evalPanSemRecursiveCallContextHOLExact
program c1 = ... c2` whenever `c1.state = c2.state` (evaluator is
insensitive to the decidability fields), proved by `fun_induction`,
then rewriting the eval-to-eval equality (which is type correct).
-/

theorem eval_context_state {width : Nat} {σ : Type} [NeZero width] (program : ProgHOL width)
    (c1 c2 : PanSemExactEvalContext width σ) (h : c1.state = c2.state) :
    evalPanSemRecursiveCallContextHOLExact program c1 =
      evalPanSemRecursiveCallContextHOLExact program c2 :=
  congrArg (evalPanSemRecursiveCallContextHOLExact program) (PanSemExactEvalContext.ext h)

end Flapjack
