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

/-! ## Step commutation with the clock shift

Flapjack-specific: each exact nonrecursive clause step commutes with
`stateAddClock`, because it only inspects non-clock fields (`ffi`, memory,
locals) and updates non-clock fields.  This is infrastructure towards the HOL
`evaluate_add_clock_eq` analogue; no declaration carries a `@[hol]` tag. -/

theorem lookupKvarHOLExact_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (kind : VarKind) (name : MlS) (state : PanSemStateExact width σ) (extra : Nat) :
    lookupKvarHOLExact kind name (stateAddClock state extra) =
      lookupKvarHOLExact kind name state := by
  cases kind <;> rfl

theorem assignStepHOLExact_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs] (kind : VarKind)
    (name : MlS) (source : ExpHOL width) (extra : Nat) :
    assignStepHOLExact (stateAddClock state extra) kind name source
        (fun _ expression => evalHOLExact (stateAddClock state extra) expression) =
      ((assignStepHOLExact state kind name source
          (fun _ expression => evalHOLExact state expression)).1,
       stateAddClock (assignStepHOLExact state kind name source
          (fun _ expression => evalHOLExact state expression)).2 extra) := by
  cases h : evalHOLExact state source with
  | none => simp only [assignStepHOLExact, evalHOLExact_stateAddClock, h]
  | some value =>
      by_cases hv : isValidValueHOLExact state kind name value = true
      · simp [assignStepHOLExact, h, hv]
      · simp [assignStepHOLExact, h, hv]

theorem primitiveStepHOLExact_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs] (name : MlS)
    (operator : PrimOp) (arguments : List (ExpHOL width)) (extra : Nat) :
    primitiveStepHOLExact (stateAddClock state extra) name operator arguments
        (fun _ expressions => evalListHOLExact (stateAddClock state extra) expressions) =
      ((primitiveStepHOLExact state name operator arguments
          (fun _ expressions => evalListHOLExact state expressions)).1,
       stateAddClock (primitiveStepHOLExact state name operator arguments
          (fun _ expressions => evalListHOLExact state expressions)).2 extra) := by
  cases h : evalListHOLExact state arguments with
  | none => simp only [primitiveStepHOLExact, evalListHOLExact_stateAddClock, h]
  | some values =>
      cases h2 : panPrimopHOLExact (width := width) operator values with
      | none => simp only [primitiveStepHOLExact, evalListHOLExact_stateAddClock, h, h2]
      | some value =>
          by_cases hv : isValidValueHOLExact state .local name value = true
          · simp [primitiveStepHOLExact, h, h2, hv]
          · simp [primitiveStepHOLExact, h, h2, hv]

theorem storeStepHOLExact_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (address value : ExpHOL width) (extra : Nat) :
    storeStepHOLExact (stateAddClock state extra) address value
        (fun _ expression => evalHOLExact (stateAddClock state extra) expression) =
      ((storeStepHOLExact state address value
          (fun _ expression => evalHOLExact state expression)).1,
       stateAddClock (storeStepHOLExact state address value
          (fun _ expression => evalHOLExact state expression)).2 extra) := by
  cases h : evalHOLExact state address with
  | none => simp only [storeStepHOLExact, evalHOLExact_stateAddClock, h]
  | some v =>
      cases v with
      | val w =>
          cases w with
          | word addr =>
              cases h2 : evalHOLExact state value with
              | none => simp only [storeStepHOLExact, evalHOLExact_stateAddClock, h, h2]
              | some v2 =>
                  cases h3 : panMemStoresHOL addr (flattenHOL v2) state.memaddrs
                      state.memory with
                  | none => simp only [storeStepHOLExact, evalHOLExact_stateAddClock, h, h2, h3]
                  | some memory =>
                      simp only [storeStepHOLExact, evalHOLExact_stateAddClock, h, h2, h3]
      | rStruct fields => simp only [storeStepHOLExact, evalHOLExact_stateAddClock, h]
      | nStruct nm fields => simp only [storeStepHOLExact, evalHOLExact_stateAddClock, h]

theorem store32StepHOLExact_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (address value : ExpHOL width) (extra : Nat) :
    store32StepHOLExact (stateAddClock state extra) address value
        (fun _ expression => evalHOLExact (stateAddClock state extra) expression) =
      ((store32StepHOLExact state address value
          (fun _ expression => evalHOLExact state expression)).1,
       stateAddClock (store32StepHOLExact state address value
          (fun _ expression => evalHOLExact state expression)).2 extra) := by
  cases h : evalHOLExact state address with
  | none => simp only [store32StepHOLExact, evalHOLExact_stateAddClock, h]
  | some v =>
      cases v with
      | val w =>
          cases w with
          | word addr =>
              cases h2 : evalHOLExact state value with
              | none => simp only [store32StepHOLExact, evalHOLExact_stateAddClock, h, h2]
              | some v2 =>
                  cases v2 with
                  | val w2 =>
                      cases w2 with
                      | word word =>
                          cases h3 : panMemStore32HOL state.memory state.memaddrs
                              state.be addr (BitVec.ofNat 32 word.toNat) with
                          | none => simp only [store32StepHOLExact, evalHOLExact_stateAddClock,
                              h, h2, h3]
                          | some memory =>
                              simp only [store32StepHOLExact, evalHOLExact_stateAddClock,
                                h, h2, h3]
                  | rStruct fields =>
                      simp only [store32StepHOLExact, evalHOLExact_stateAddClock, h, h2]
                  | nStruct nm fields =>
                      simp only [store32StepHOLExact, evalHOLExact_stateAddClock, h, h2]
      | rStruct fields => simp only [store32StepHOLExact, evalHOLExact_stateAddClock, h]
      | nStruct nm fields => simp only [store32StepHOLExact, evalHOLExact_stateAddClock, h]

theorem storeByteStepHOLExact_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (address value : ExpHOL width) (extra : Nat) :
    storeByteStepHOLExact (stateAddClock state extra) address value
        (fun _ expression => evalHOLExact (stateAddClock state extra) expression) =
      ((storeByteStepHOLExact state address value
          (fun _ expression => evalHOLExact state expression)).1,
       stateAddClock (storeByteStepHOLExact state address value
          (fun _ expression => evalHOLExact state expression)).2 extra) := by
  cases h : evalHOLExact state address with
  | none => simp only [storeByteStepHOLExact, evalHOLExact_stateAddClock, h]
  | some v =>
      cases v with
      | val w =>
          cases w with
          | word addr =>
              cases h2 : evalHOLExact state value with
              | none => simp only [storeByteStepHOLExact, evalHOLExact_stateAddClock, h, h2]
              | some v2 =>
                  cases v2 with
                  | val w2 =>
                      cases w2 with
                      | word word =>
                          cases h3 : panMemStoreByteHOL state.memory state.memaddrs
                              state.be addr (UInt8.ofNat word.toNat) with
                          | none => simp only [storeByteStepHOLExact, evalHOLExact_stateAddClock,
                              h, h2, h3]
                          | some memory =>
                              simp only [storeByteStepHOLExact, evalHOLExact_stateAddClock,
                                h, h2, h3]
                  | rStruct fields =>
                      simp only [storeByteStepHOLExact, evalHOLExact_stateAddClock, h, h2]
                  | nStruct nm fields =>
                      simp only [storeByteStepHOLExact, evalHOLExact_stateAddClock, h, h2]
      | rStruct fields => simp only [storeByteStepHOLExact, evalHOLExact_stateAddClock, h]
      | nStruct nm fields => simp only [storeByteStepHOLExact, evalHOLExact_stateAddClock, h]

theorem returnStepHOLExact_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (expression : ExpHOL width) (extra : Nat) :
    returnStepHOLExact (stateAddClock state extra) expression
        (fun _ e => evalHOLExact (stateAddClock state extra) e) =
      ((returnStepHOLExact state expression (fun _ e => evalHOLExact state e)).1,
       stateAddClock (returnStepHOLExact state expression
          (fun _ e => evalHOLExact state e)).2 extra) := by
  cases h : evalHOLExact state expression with
  | none => simp only [returnStepHOLExact, evalHOLExact_stateAddClock, h]
  | some value =>
      by_cases hs : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL state.structs
          (shapeOfHOLExact value) ≤ 32
      · simp [returnStepHOLExact, h, hs]
      · simp [returnStepHOLExact, h, hs]

theorem raiseStepHOLExact_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (exceptionId : MlS) (expression : ExpHOL width) (extra : Nat) :
    raiseStepHOLExact (stateAddClock state extra) exceptionId expression
        (fun _ e => evalHOLExact (stateAddClock state extra) e) =
      ((raiseStepHOLExact state exceptionId expression
          (fun _ e => evalHOLExact state e)).1,
       stateAddClock (raiseStepHOLExact state exceptionId expression
          (fun _ e => evalHOLExact state e)).2 extra) := by
  cases h : evalHOLExact state expression with
  | none => simp only [raiseStepHOLExact, evalHOLExact_stateAddClock, h]
  | some value =>
      cases h2 : state.eshapes exceptionId with
      | none => simp only [raiseStepHOLExact, evalHOLExact_stateAddClock, h, h2]
      | some shape =>
          by_cases h3 : shapeEqHOL (shapeOfHOLExact value) shape = true
          · by_cases h4 : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL state.structs
                (shapeOfHOLExact value) ≤ 32
            · simp [raiseStepHOLExact, h, h2, h3, h4]
            · simp [raiseStepHOLExact, h, h2, h3, h4]
          · simp [raiseStepHOLExact, h, h2, h3]

theorem tickStepHOLExact_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (extra : Nat) (h : state.clock ≠ 0) :
    tickStepHOLExact (stateAddClock state extra) =
      ((tickStepHOLExact state).1, stateAddClock (tickStepHOLExact state).2 extra) := by
  rw [tickStepHOLExact_clock_pos state h]
  have h' : (stateAddClock state extra).clock ≠ 0 := by
    simp only []; omega
  rw [tickStepHOLExact_clock_pos _ h']
  exact congrArg (fun s => (none, s)) (decClockHOLExact_stateAddClock state extra h)

theorem shMemLoadHOLExact_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    (kind : VarKind) (name : MlS) (address : RiscV.Word width) (nb : Nat) (extra : Nat) :
    shMemLoadHOLExact (stateAddClock state extra) kind name address nb =
      ((shMemLoadHOLExact state kind name address nb).1,
       stateAddClock (shMemLoadHOLExact state kind name address nb).2 extra) := by
  unfold shMemLoadHOLExact
  simp only [stateAddClock]
  by_cases hnb : nb = 0
  · subst hnb
    simp only [if_true]
    by_cases hdom : state.shMemaddrs address
    · simp only [hdom, if_true]
      cases hf : callFFIHOL state.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 0]
          (panWordToBytesHOL address false) with
      | final ev => simp only [emptyLocalsHOLExact_stateAddClock]
      | ret nf nb' => simp only [setKvarHOLExact_stateAddClock]
    · simp only [hdom, if_false]
  · simp only [hnb, if_false]
    by_cases hdom : state.shMemaddrs (panByteAlignHOL address)
    · simp only [hdom, if_true]
      cases hf : callFFIHOL state.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
          (panWordToBytesHOL address false) with
      | final ev => simp only [emptyLocalsHOLExact_stateAddClock]
      | ret nf nb' => simp only [setKvarHOLExact_stateAddClock]
    · simp only [hdom, if_false]

theorem shMemStoreHOLExact_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    (word : RiscV.Word width) (address : RiscV.Word width) (nb : Nat) (extra : Nat) :
    shMemStoreHOLExact (stateAddClock state extra) word address nb =
      ((shMemStoreHOLExact state word address nb).1,
       stateAddClock (shMemStoreHOLExact state word address nb).2 extra) := by
  unfold shMemStoreHOLExact
  simp only [stateAddClock]
  by_cases hnb : nb = 0
  · subst hnb
    simp only [if_true]
    by_cases hdom : state.shMemaddrs address
    · simp only [hdom, if_true]
      cases hf : callFFIHOL state.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 0]
          (panWordToBytesHOL word false ++ panWordToBytesHOL address false) with
      | final ev => simp only []
      | ret nf nb' => simp only []
    · simp only [hdom, if_false]
  · simp only [hnb, if_false]
    by_cases hdom : state.shMemaddrs (panByteAlignHOL address)
    · simp only [hdom, if_true]
      cases hf : callFFIHOL state.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 nb]
          ((panWordToBytesHOL word false).take nb ++ panWordToBytesHOL address false) with
      | final ev => simp only []
      | ret nf nb' => simp only []
    · simp only [hdom, if_false]

theorem extCallStepHOLExact_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (function : MlS) (ptr1 len1 ptr2 len2 : ExpHOL width) (extra : Nat) :
    extCallStepHOLExact (stateAddClock state extra)
        (fun _ e => evalHOLExact (stateAddClock state extra) e) function ptr1 len1 ptr2 len2 =
      ((extCallStepHOLExact state (fun _ e => evalHOLExact state e) function ptr1 len1 ptr2 len2).1,
       stateAddClock (extCallStepHOLExact state (fun _ e => evalHOLExact state e) function
          ptr1 len1 ptr2 len2).2 extra) := by
  unfold extCallStepHOLExact
  simp only [evalHOLExact_stateAddClock]
  cases h1 : evalHOLExact state ptr1 with
  | none => simp only []
  | some v1 =>
    cases v1 with
    | val w1 =>
      cases w1 with
      | word a1 =>
        cases h2 : evalHOLExact state len1 with
        | none => simp only []
        | some v2 =>
          cases v2 with
          | val w2 =>
            cases w2 with
            | word l1 =>
              cases h3 : evalHOLExact state ptr2 with
              | none => simp only []
              | some v3 =>
                cases v3 with
                | val w3 =>
                  cases w3 with
                  | word a2 =>
                    cases h4 : evalHOLExact state len2 with
                    | none => simp only []
                    | some v4 =>
                      cases v4 with
                      | val w4 =>
                        cases w4 with
                        | word l2 =>
                          cases hr1 : readBytearrayWordHOL (byteWidth := 8) a1 l1.toNat
                              (panMemLoadByteWord8HOL state.memory state.memaddrs state.be) with
                          | none => simp only [hr1]
                          | some b1 =>
                            cases hr2 : readBytearrayWordHOL (byteWidth := 8) a2 l2.toNat
                                (panMemLoadByteWord8HOL state.memory state.memaddrs state.be) with
                            | none => simp only [hr1, hr2]
                            | some b2 =>
                              cases hf : callFFIHOL state.ffi (.extCall function)
                                  b1 b2 with
                              | final ev => simp only [hr1, hr2, hf,
                                  emptyLocalsHOLExact_stateAddClock]
                              | ret nf nb' => simp only [hr1, hr2, hf]
                      | rStruct fields => simp only []
                      | nStruct nm fields => simp only []
                | rStruct fields => simp only []
                | nStruct nm fields => simp only []
          | rStruct fields => simp only []
          | nStruct nm fields => simp only []
    | rStruct fields => simp only []
    | nStruct nm fields => simp only []

theorem shMemLoadClauseHOLExact_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    [DecidablePred state.memaddrs]
    (operator : OpSize) (kind : VarKind) (name : MlS) (address : ExpHOL width) (extra : Nat) :
    shMemLoadClauseHOLExact (stateAddClock state extra) operator kind name address
        (fun _ e => evalHOLExact (stateAddClock state extra) e) =
      ((shMemLoadClauseHOLExact state operator kind name address
          (fun _ e => evalHOLExact state e)).1,
       stateAddClock (shMemLoadClauseHOLExact state operator kind name address
          (fun _ e => evalHOLExact state e)).2 extra) := by
  unfold shMemLoadClauseHOLExact
  simp only [evalHOLExact_stateAddClock]
  cases h : evalHOLExact state address with
  | none => simp only []
  | some v =>
      cases v with
      | val w =>
          cases w with
          | word addr =>
              cases hl : lookupKvarHOLExact kind name state with
              | none => simp only [hl, lookupKvarHOLExact_stateAddClock]
              | some lv =>
                  cases lv with
                  | val w2 =>
                      cases w2 with
                      | word word =>
                          simp only [hl, lookupKvarHOLExact_stateAddClock]
                          rw [shMemLoadHOLExact_stateAddClock]
                  | rStruct fields => simp only [hl, lookupKvarHOLExact_stateAddClock]
                  | nStruct nm fields => simp only [hl, lookupKvarHOLExact_stateAddClock]
      | rStruct fields => simp only []
      | nStruct nm fields => simp only []

theorem shMemStoreClauseHOLExact_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    [DecidablePred state.memaddrs]
    (operator : OpSize) (address value : ExpHOL width) (extra : Nat) :
    shMemStoreClauseHOLExact (stateAddClock state extra) operator address value
        (fun _ e => evalHOLExact (stateAddClock state extra) e) =
      ((shMemStoreClauseHOLExact state operator address value
          (fun _ e => evalHOLExact state e)).1,
       stateAddClock (shMemStoreClauseHOLExact state operator address value
          (fun _ e => evalHOLExact state e)).2 extra) := by
  unfold shMemStoreClauseHOLExact
  simp only [evalHOLExact_stateAddClock]
  cases h : evalHOLExact state address with
  | none => simp only []
  | some v =>
      cases v with
      | val w =>
          cases w with
          | word addr =>
              cases h2 : evalHOLExact state value with
              | none => simp only []
              | some v2 =>
                  cases v2 with
                  | val w2 =>
                      cases w2 with
                      | word word =>
                          simp only []
                          rw [shMemStoreHOLExact_stateAddClock]
                  | rStruct fields => simp only []
                  | nStruct nm fields => simp only []
      | rStruct fields => simp only []
      | nStruct nm fields => simp only []

theorem callFixedContextHOLExact_callEntry_stateAddClock_state
    {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (calleeLocals : MlS → Option (ValueHOL width))
    (bodyResult : Option (PanSemResultExact width))
    (bodyContext : PanSemExactEvalContext width σ) (extra : Nat) (h : state.clock ≠ 0) :
    (callFixedContextHOLExact (callEntryStateHOLExact (stateAddClock state extra) calleeLocals)
        bodyResult (ctxAddClock bodyContext extra)).state =
      stateAddClock (callFixedContextHOLExact (callEntryStateHOLExact state calleeLocals)
        bodyResult bodyContext).state extra := by
  show (fixClockHOLExact (callEntryStateHOLExact (stateAddClock state extra) calleeLocals)
      (bodyResult, stateAddClock bodyContext.state extra)).2 =
    stateAddClock (fixClockHOLExact (callEntryStateHOLExact state calleeLocals)
      (bodyResult, bodyContext.state)).2 extra
  rw [callEntryStateHOLExact_stateAddClock state calleeLocals extra h]
  exact congrArg Prod.snd (fixClockHOLExact_stateAddClock_pair (callEntryStateHOLExact state calleeLocals)
    bodyResult bodyContext.state extra)

theorem callFixedContextHOLExact_callEntry_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (calleeLocals : MlS → Option (ValueHOL width))
    (bodyResult : Option (PanSemResultExact width))
    (bodyContext : PanSemExactEvalContext width σ) (extra : Nat) (h : state.clock ≠ 0) :
    callFixedContextHOLExact (callEntryStateHOLExact (stateAddClock state extra) calleeLocals)
        bodyResult (ctxAddClock bodyContext extra) =
      ctxAddClock (callFixedContextHOLExact (callEntryStateHOLExact state calleeLocals)
        bodyResult bodyContext) extra := by
  apply PanSemExactEvalContext.ext
  exact callFixedContextHOLExact_callEntry_stateAddClock_state state calleeLocals
    bodyResult bodyContext extra h

theorem handlerStateHOLExact_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (context : PanSemExactEvalContext width σ) (fixedContext : PanSemExactEvalContext width σ)
    (name : MlS) (value : ValueHOL width) (extra : Nat) :
    handlerStateHOLExact (ctxAddClock context extra) (ctxAddClock fixedContext extra) name value =
      stateAddClock (handlerStateHOLExact context fixedContext name value) extra := by
  have h1 := setVarHOLExact_stateAddClock name value
      { fixedContext.state with locals := context.state.locals } extra
  have h2 : { (ctxAddClock fixedContext extra).state with
        locals := (ctxAddClock context extra).state.locals } =
      stateAddClock { fixedContext.state with locals := context.state.locals } extra := rfl
  unfold handlerStateHOLExact
  rw [h2, h1]

theorem callFixedContextHOLExact_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (entry : PanSemStateExact width σ) (bodyResult : Option (PanSemResultExact width))
    (bodyContext : PanSemExactEvalContext width σ) (extra : Nat) :
    callFixedContextHOLExact (stateAddClock entry extra) bodyResult
        (ctxAddClock bodyContext extra) =
      ctxAddClock (callFixedContextHOLExact entry bodyResult bodyContext) extra := by
  apply PanSemExactEvalContext.ext
  simp only [callFixedContextHOLExact]
  exact congrArg Prod.snd (fixClockHOLExact_stateAddClock_pair entry bodyResult bodyContext.state extra)

theorem callContinuationContextHOLExact_stateAddClock {width : Nat} {σ : Type} [NeZero width]
    (context : PanSemExactEvalContext width σ) (fixedContext : PanSemExactEvalContext width σ)
    (resultName : MlS) (value : ValueHOL width) (extra : Nat) :
    callContinuationContextHOLExact (ctxAddClock context extra) (ctxAddClock fixedContext extra)
        resultName value =
      ctxAddClock (callContinuationContextHOLExact context fixedContext resultName value) extra := by
  apply PanSemExactEvalContext.ext
  simp only [callContinuationContextHOLExact]
  exact handlerStateHOLExact_stateAddClock context fixedContext resultName value extra

end Flapjack
