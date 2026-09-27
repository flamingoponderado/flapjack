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

/-! ## Note (bead flapjack-dpvn)

The `withState`-built evaluation contexts make direct rewriting of the
longer run's recursive-call context impossible: the equation compiler
generates opaque proof terms for the `DecidablePred` fields, e.g.
`evalPanSemRecursiveCallContextHOLExact._proof_5 (ctxAddClock context
extra) ...`, which are propositionally equal to the simple `rfl` proofs
used by the helper lemmas but cannot be matched by `rw`/`simp` at the
implicit transparency level.  The workaround is the bridge
`eval_context_state`: the evaluator is insensitive to the decidability
fields, so an eval-to-eval equality follows from a state equality.  With
that bridge, the result-agreement lemma `eval_add_clock_mono_aux` below
is proved by `fun_induction` over the recursive evaluator.
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


attribute [local simp] PanSemExactEvalContext.withState_state

macro "closeLeaf" : tactic => `(tactic|
  (intro extra resultLow resultHigh hLow hHigh) <;>
  (try (cases hLow)) <;>
  (rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh) <;>
  dsimp only at hHigh <;>
  simp only [evalHOLExact_stateAddClock, evalListHOLExact_stateAddClock,
    isValidValueHOLExact_stateAddClock] at hHigh <;>
  (try (split at hHigh)) <;>
  (try (split at hHigh)) <;>
  (try (split at hHigh)) <;>
  (try (split at hHigh)) <;>
  (try (split at hHigh)) <;>
  (try (split at hHigh)) <;>
  (try (simp_all (config := { zetaDelta := true }))) <;>
  (try (rw [← hHigh])) <;>
  (try (simp_all (config := { zetaDelta := true }))) <;>
  (try (rw [PanSemExactEvalContext.withState_state])) <;>
  (try (exact List.prefix_refl _)) <;>
  (try (simp only [PanSemExactEvalContext.withState_state, List.prefix_refl])))

theorem callFixedContextHOLExact_state_ffi {width : Nat} {σ : Type} [NeZero width]
    (entry : PanSemStateExact width σ) (bodyResult : Option (PanSemResultExact width))
    (bodyContext : PanSemExactEvalContext width σ) :
    (callFixedContextHOLExact entry bodyResult bodyContext).state.ffi = bodyContext.state.ffi := by
  simp only [callFixedContextHOLExact, PanSemExactEvalContext.withState_state, fixClockHOLExact]


set_option maxHeartbeats 4000000 in
theorem eval_add_clock_mono_aux
    {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) (context : PanSemExactEvalContext width σ) :
    ∀ (extra : Nat)
      (resultLow resultHigh : Option (PanSemResultExact width) × PanSemExactEvalContext width σ),
      evalPanSemRecursiveCallContextHOLExact program context = some resultLow →
      evalPanSemRecursiveCallContextHOLExact program (ctxAddClock context extra) = some resultHigh →
      resultLow.2.state.ffi.ioEvents <+: resultHigh.2.state.ffi.ioEvents ∧
      (resultLow.1 ≠ some .timeOut →
        resultHigh = (resultLow.1, ctxAddClock resultLow.2 extra)) := by
  fun_induction evalPanSemRecursiveCallContextHOLExact program context
  case case3 =>
    rename_i inst context state name shape initializer body value hval hshape bodyState bodyContext
      result postContext hrec restored ih1
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalHOLExact_stateAddClock] at hHigh
    rw [show evalHOLExact context.state initializer = some value from hval] at hHigh
    simp only [hshape, if_true] at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rH cH hbodyH
      simp only [Option.some.injEq] at hHigh
      have hbodyH' : evalPanSemRecursiveCallContextHOLExact body (ctxAddClock bodyContext extra) =
          some (rH, cH) := by
        rw [← eval_context_state body _ (ctxAddClock bodyContext extra)]
        · exact hbodyH
        · rfl
      have hih := ih1 extra (result, postContext) (rH, cH) hrec hbodyH'
      rw [← hHigh]
      constructor
      · simpa only [PanSemExactEvalContext.withState_state] using hih.1
      · intro hne
        obtain ⟨hrH, hcH⟩ := Prod.mk.inj (hih.2 hne)
        subst hrH
        subst hcH
        congr 1
  case case6 =>
    rename_i inst context state first second postContext hfirst fixed fixedContext ih2 ih1
    intro extra resultLow resultHigh hLow hHigh
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rF cF hfirstHigh
      have hih2 := ih2 extra (none, postContext) (rF, cF) hfirst hfirstHigh
      obtain ⟨hrF, hcF⟩ := Prod.mk.inj (hih2.2 (by simp))
      subst rF
      subst cF
      try simp only [] at hHigh
      have hbodyH' : evalPanSemRecursiveCallContextHOLExact second (ctxAddClock fixedContext extra) =
          some resultHigh := by
        rw [← eval_context_state second _ (ctxAddClock fixedContext extra)]
        · exact hHigh
        · exact congrArg PanSemExactEvalContext.state
            (ctxAddClock_withState_fixClock postContext context.state none extra)
      exact ih1 extra resultLow resultHigh hLow hbodyH'
  case case7 =>
    rename_i inst context state first second postContext val hfirst fixed fixedContext ih1
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rF cF hfirstHigh
      have hih1 := ih1 extra (some val, postContext) (rF, cF) hfirst hfirstHigh
      have hpref := hih1.1
      try simp only [] at hpref
      cases rF with
      | none =>
          dsimp only at hHigh
          have hsp := evalPanSemRecursiveCallContextHOLExact_ioEvents_prefix second _ resultHigh hHigh
          constructor
          · exact hpref.trans hsp
          · intro hne
            obtain ⟨hrF, _⟩ := Prod.mk.inj (hih1.2 hne)
            exact absurd hrF (by simp)
      | some rF' =>
          simp only [Option.some.injEq] at hHigh
          rw [← hHigh]
          constructor
          · exact hpref
          · intro hne
            obtain ⟨hrF, hcF⟩ := Prod.mk.inj (hih1.2 hne)
            cases hrF
            cases hcF
            congr 1
            apply PanSemExactEvalContext.ext
            try simp only []
            exact congrArg Prod.snd
              (fixClockHOLExact_stateAddClock_pair state (some val) postContext.state extra)
  case case8 =>
    rename_i inst context state condition thenBranch elseBranch value hcond hw ih1
    intro extra resultLow resultHigh hLow hHigh
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalHOLExact_stateAddClock] at hHigh
    rw [show evalHOLExact context.state condition = some (ValueHOL.val (HolWordLab.word value)) from hcond]
      at hHigh
    simp only [hw, if_true] at hHigh
    exact ih1 extra resultLow resultHigh hLow hHigh
  case case9 =>
    rename_i inst context state condition thenBranch elseBranch value hcond hw ih1
    intro extra resultLow resultHigh hLow hHigh
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalHOLExact_stateAddClock] at hHigh
    rw [show evalHOLExact context.state condition = some (ValueHOL.val (HolWordLab.word value)) from hcond]
      at hHigh
    simp only [hw] at hHigh
    exact ih1 extra resultLow resultHigh hLow hHigh
  case case11 =>
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    constructor
    · have hprefix := evalPanSemRecursiveCallContextHOLExact_ioEvents_prefix
          _ _ resultHigh hHigh
      exact hprefix
    · intro hne; exact absurd rfl hne
  case case13 =>
    rename_i inst context state condition body value hcond hw hclock entry entryContext postContext
      hrec fixed fixedContext ih2 ih1
    intro extra resultLow resultHigh hLow hHigh
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalHOLExact_stateAddClock] at hHigh
    rw [show evalHOLExact context.state condition = some (ValueHOL.val (HolWordLab.word value)) from hcond]
      at hHigh
    dsimp only at hHigh
    rw [if_pos hw] at hHigh
    rw [if_neg (by have hc : context.state.clock ≠ 0 := hclock; omega)] at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rB cB hbodyH
      have hbodyH' : evalPanSemRecursiveCallContextHOLExact body (ctxAddClock entryContext extra) =
          some (rB, cB) := by
        rw [← eval_context_state body _ (ctxAddClock entryContext extra)]
        · exact hbodyH
        · change decClockHOLExact (stateAddClock context.state extra) = stateAddClock entry extra
          rw [decClockHOLExact_stateAddClock context.state extra hclock]
      have hih2 := ih2 extra (some .continue, postContext) (rB, cB) hrec hbodyH'
      obtain ⟨hrB, hcB⟩ := Prod.mk.inj (hih2.2 (by simp))
      cases hrB
      cases hcB
      have hHigh' : evalPanSemRecursiveCallContextHOLExact (.while condition body)
          (ctxAddClock fixedContext extra) = some resultHigh := by
        rw [← eval_context_state _ _ (ctxAddClock fixedContext extra)]
        · exact hHigh
        · change (fixClockHOLExact (decClockHOLExact (stateAddClock context.state extra))
              (some PanSemResultExact.continue, (ctxAddClock postContext extra).state)).snd =
            stateAddClock (fixClockHOLExact entry (some (PanSemResultExact.continue), postContext.state)).snd extra
          rw [decClockHOLExact_stateAddClock context.state extra hclock]
          exact congrArg Prod.snd
            (fixClockHOLExact_stateAddClock_pair entry (some (PanSemResultExact.continue))
              postContext.state extra)
      exact ih1 extra resultLow resultHigh hLow hHigh'
  case case14 =>
    rename_i inst context state condition body value hcond hw hclock entry entryContext postContext
      hrec fixed fixedContext ih2 ih1
    intro extra resultLow resultHigh hLow hHigh
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalHOLExact_stateAddClock] at hHigh
    rw [show evalHOLExact context.state condition = some (ValueHOL.val (HolWordLab.word value)) from hcond]
      at hHigh
    dsimp only at hHigh
    rw [if_pos hw] at hHigh
    rw [if_neg (by have hc : context.state.clock ≠ 0 := hclock; omega)] at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rB cB hbodyH
      have hbodyH' : evalPanSemRecursiveCallContextHOLExact body (ctxAddClock entryContext extra) =
          some (rB, cB) := by
        rw [← eval_context_state body _ (ctxAddClock entryContext extra)]
        · exact hbodyH
        · change decClockHOLExact (stateAddClock context.state extra) = stateAddClock entry extra
          rw [decClockHOLExact_stateAddClock context.state extra hclock]
      have hih2 := ih2 extra (none, postContext) (rB, cB) hrec hbodyH'
      obtain ⟨hrB, hcB⟩ := Prod.mk.inj (hih2.2 (by simp))
      cases hrB
      cases hcB
      have hHigh' : evalPanSemRecursiveCallContextHOLExact (.while condition body)
          (ctxAddClock fixedContext extra) = some resultHigh := by
        rw [← eval_context_state _ _ (ctxAddClock fixedContext extra)]
        · exact hHigh
        · change (fixClockHOLExact (decClockHOLExact (stateAddClock context.state extra))
              ((none : Option (PanSemResultExact width)), (ctxAddClock postContext extra).state)).snd =
            stateAddClock (fixClockHOLExact entry
              ((none : Option (PanSemResultExact width)), postContext.state)).snd extra
          rw [decClockHOLExact_stateAddClock context.state extra hclock]
          exact congrArg Prod.snd
            (fixClockHOLExact_stateAddClock_pair entry
              ((none : Option (PanSemResultExact width))) postContext.state extra)
      exact ih1 extra resultLow resultHigh hLow hHigh'
  case case15 =>
    rename_i inst context state condition body value hcond hw hclock entry entryContext postContext
      hrec fixed fixedContext ih1
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalHOLExact_stateAddClock] at hHigh
    rw [show evalHOLExact context.state condition = some (ValueHOL.val (HolWordLab.word value)) from hcond]
      at hHigh
    dsimp only at hHigh
    rw [if_pos hw] at hHigh
    rw [if_neg (by have hc : context.state.clock ≠ 0 := hclock; omega)] at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rB cB hbodyH
      have hbodyH' : evalPanSemRecursiveCallContextHOLExact body (ctxAddClock entryContext extra) =
          some (rB, cB) := by
        rw [← eval_context_state body _ (ctxAddClock entryContext extra)]
        · exact hbodyH
        · change decClockHOLExact (stateAddClock context.state extra) = stateAddClock entry extra
          rw [decClockHOLExact_stateAddClock context.state extra hclock]
      have hih1 := ih1 extra (some .break, postContext) (rB, cB) hrec hbodyH'
      obtain ⟨hrB, hcB⟩ := Prod.mk.inj (hih1.2 (by simp))
      cases hrB
      cases hcB
      simp only [Option.some.injEq] at hHigh
      rw [← hHigh]
      constructor
      · exact hih1.1
      · intro _
        congr 1
        apply PanSemExactEvalContext.ext
        change (fixClockHOLExact (decClockHOLExact (stateAddClock context.state extra))
              (some (PanSemResultExact.break), (ctxAddClock postContext extra).state)).snd =
            stateAddClock (fixClockHOLExact entry (some (PanSemResultExact.break), postContext.state)).snd extra
        rw [decClockHOLExact_stateAddClock context.state extra hclock]
        exact congrArg Prod.snd
          (fixClockHOLExact_stateAddClock_pair entry (some (PanSemResultExact.break))
            postContext.state extra)
  case case16 =>
    rename_i inst context state condition body value hcond hw hclock entry entryContext result postContext
      hbody fixed fixedContext hcont hnone hbreak ih1
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalHOLExact_stateAddClock] at hHigh
    rw [show evalHOLExact context.state condition = some (ValueHOL.val (HolWordLab.word value)) from hcond]
      at hHigh
    dsimp only at hHigh
    rw [if_pos hw] at hHigh
    rw [if_neg (by have hc : context.state.clock ≠ 0 := hclock; omega)] at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rB cB hbodyH
      have hbodyH' : evalPanSemRecursiveCallContextHOLExact body (ctxAddClock entryContext extra) =
          some (rB, cB) := by
        rw [← eval_context_state body _ (ctxAddClock entryContext extra)]
        · exact hbodyH
        · change decClockHOLExact (stateAddClock context.state extra) = stateAddClock entry extra
          rw [decClockHOLExact_stateAddClock context.state extra hclock]
      have hih1 := ih1 extra (result, postContext) (rB, cB) hbody hbodyH'
      have hpref : postContext.state.ffi.ioEvents <+: cB.state.ffi.ioEvents := hih1.1
      by_cases hto : result = some .timeOut
      · constructor
        · split at hHigh
          · have hsp := evalPanSemRecursiveCallContextHOLExact_ioEvents_prefix _ _ resultHigh hHigh
            simp only [PanSemExactEvalContext.withState_state, fixClockHOLExact] at hsp ⊢
            exact hpref.trans hsp
          · have hsp := evalPanSemRecursiveCallContextHOLExact_ioEvents_prefix _ _ resultHigh hHigh
            simp only [PanSemExactEvalContext.withState_state, fixClockHOLExact] at hsp ⊢
            exact hpref.trans hsp
          · simp only [Option.some.injEq] at hHigh
            subst resultHigh
            simp only [PanSemExactEvalContext.withState_state, fixClockHOLExact]
            exact hpref
          · simp only [Option.some.injEq] at hHigh
            subst resultHigh
            simp only [PanSemExactEvalContext.withState_state, fixClockHOLExact]
            exact hpref
        · intro hne; exact absurd hto hne
      · have hpin := hih1.2 hto
        obtain ⟨hrB, hcB⟩ := Prod.mk.inj hpin
        cases hrB
        cases hcB
        split at hHigh
        · simp_all
        · simp_all
        · simp_all
        · simp only [Option.some.injEq] at hHigh
          rw [← hHigh]
          constructor
          · simp only [PanSemExactEvalContext.withState_state, fixClockHOLExact]
            exact hpref
          · intro _
            congr 1
            apply PanSemExactEvalContext.ext
            change (fixClockHOLExact (decClockHOLExact (stateAddClock context.state extra))
                  (result, (ctxAddClock postContext extra).state)).snd =
                stateAddClock (fixClockHOLExact entry (result, postContext.state)).snd extra
            rw [decClockHOLExact_stateAddClock context.state extra hclock]
            exact congrArg Prod.snd
              (fixClockHOLExact_stateAddClock_pair entry result postContext.state extra)
  case case17 =>
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalHOLExact_stateAddClock] at hHigh
    simp_all (config := { zetaDelta := true })
    subst resultHigh
    try simp only []
    exact List.prefix_refl _
  case case21 =>
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    constructor
    · have hprefix := evalPanSemRecursiveCallContextHOLExact_ioEvents_prefix
          _ _ resultHigh hHigh
      exact hprefix
    · intro hne; exact absurd rfl hne
  case case23 =>
    rename_i inst context state info function arguments values hargs body calleeLocals returnShape
      hlookup hclock entry entryContext postContext hbody fixedContext ih1
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalListHOLExact_stateAddClock] at hHigh
    rw [show evalListHOLExact context.state arguments = some values from hargs] at hHigh
    try simp only [] at hHigh
    rw [show lookupCodeHOLExact context.state.code function values = some (body, calleeLocals, returnShape) from hlookup] at hHigh
    try simp only [] at hHigh
    rw [if_neg (by have hc : context.state.clock ≠ 0 := hclock; omega)] at hHigh
    try simp only [] at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rB cB hbodyH
      have hbodyH' : evalPanSemRecursiveCallContextHOLExact body (ctxAddClock entryContext extra) =
          some (rB, cB) := by
        rw [← eval_context_state body _ (ctxAddClock entryContext extra)]
        · exact hbodyH
        · change callEntryStateHOLExact (stateAddClock context.state extra) calleeLocals = stateAddClock entry extra
          rw [callEntryStateHOLExact_stateAddClock context.state calleeLocals extra hclock]
      have hih1 := ih1 extra (none, postContext) (rB, cB) hbody hbodyH'
      obtain ⟨hrB, hcB⟩ := Prod.mk.inj (hih1.2 (by simp))
      cases hrB
      cases hcB
      try simp only [] at hHigh
      rw [callFixedContextHOLExact_callEntry_stateAddClock context.state calleeLocals (none) postContext extra hclock] at hHigh
      simp only [Option.some.injEq] at hHigh
      rw [← hHigh]
      exact ⟨List.prefix_refl _, by intro _; rfl⟩
  case case24 =>
    rename_i inst context state info function arguments values hargs body calleeLocals returnShape
      hlookup hclock entry entryContext postContext hbody fixedContext ih1
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalListHOLExact_stateAddClock] at hHigh
    rw [show evalListHOLExact context.state arguments = some values from hargs] at hHigh
    try simp only [] at hHigh
    rw [show lookupCodeHOLExact context.state.code function values = some (body, calleeLocals, returnShape) from hlookup] at hHigh
    try simp only [] at hHigh
    rw [if_neg (by have hc : context.state.clock ≠ 0 := hclock; omega)] at hHigh
    try simp only [] at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rB cB hbodyH
      have hbodyH' : evalPanSemRecursiveCallContextHOLExact body (ctxAddClock entryContext extra) =
          some (rB, cB) := by
        rw [← eval_context_state body _ (ctxAddClock entryContext extra)]
        · exact hbodyH
        · change callEntryStateHOLExact (stateAddClock context.state extra) calleeLocals = stateAddClock entry extra
          rw [callEntryStateHOLExact_stateAddClock context.state calleeLocals extra hclock]
      have hih1 := ih1 extra (some .break, postContext) (rB, cB) hbody hbodyH'
      obtain ⟨hrB, hcB⟩ := Prod.mk.inj (hih1.2 (by simp))
      cases hrB
      cases hcB
      try simp only [] at hHigh
      rw [callFixedContextHOLExact_callEntry_stateAddClock context.state calleeLocals (some .break) postContext extra hclock] at hHigh
      simp only [Option.some.injEq] at hHigh
      rw [← hHigh]
      exact ⟨List.prefix_refl _, by intro _; rfl⟩
  case case25 =>
    rename_i inst context state info function arguments values hargs body calleeLocals returnShape
      hlookup hclock entry entryContext postContext hbody fixedContext ih1
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalListHOLExact_stateAddClock] at hHigh
    rw [show evalListHOLExact context.state arguments = some values from hargs] at hHigh
    try simp only [] at hHigh
    rw [show lookupCodeHOLExact context.state.code function values = some (body, calleeLocals, returnShape) from hlookup] at hHigh
    try simp only [] at hHigh
    rw [if_neg (by have hc : context.state.clock ≠ 0 := hclock; omega)] at hHigh
    try simp only [] at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rB cB hbodyH
      have hbodyH' : evalPanSemRecursiveCallContextHOLExact body (ctxAddClock entryContext extra) =
          some (rB, cB) := by
        rw [← eval_context_state body _ (ctxAddClock entryContext extra)]
        · exact hbodyH
        · change callEntryStateHOLExact (stateAddClock context.state extra) calleeLocals = stateAddClock entry extra
          rw [callEntryStateHOLExact_stateAddClock context.state calleeLocals extra hclock]
      have hih1 := ih1 extra (some .continue, postContext) (rB, cB) hbody hbodyH'
      obtain ⟨hrB, hcB⟩ := Prod.mk.inj (hih1.2 (by simp))
      cases hrB
      cases hcB
      try simp only [] at hHigh
      rw [callFixedContextHOLExact_callEntry_stateAddClock context.state calleeLocals (some .continue) postContext extra hclock] at hHigh
      simp only [Option.some.injEq] at hHigh
      rw [← hHigh]
      exact ⟨List.prefix_refl _, by intro _; rfl⟩
  case case26 =>
    rename_i inst context state function arguments values hargs body calleeLocals returnShape
      hlookup hclock entry entryContext postContext value hshape hbody fixedContext ih1
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalListHOLExact_stateAddClock] at hHigh
    rw [show evalListHOLExact context.state arguments = some values from hargs] at hHigh
    try simp only [] at hHigh
    rw [show lookupCodeHOLExact context.state.code function values = some (body, calleeLocals, returnShape) from hlookup] at hHigh
    try simp only [] at hHigh
    rw [if_neg (by have hc : context.state.clock ≠ 0 := hclock; omega)] at hHigh
    try simp only [] at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rB cB hbodyH
      have hbodyH' : evalPanSemRecursiveCallContextHOLExact body (ctxAddClock entryContext extra) =
          some (rB, cB) := by
        rw [← eval_context_state body _ (ctxAddClock entryContext extra)]
        · exact hbodyH
        · change callEntryStateHOLExact (stateAddClock context.state extra) calleeLocals = stateAddClock entry extra
          rw [callEntryStateHOLExact_stateAddClock context.state calleeLocals extra hclock]
      have hih1 := ih1 extra ((some (.returned value)), postContext) (rB, cB) hbody hbodyH'
      obtain ⟨hrB, hcB⟩ := Prod.mk.inj (hih1.2 (by simp))
      cases hrB
      cases hcB
      try simp only [] at hHigh
      rw [if_pos hshape] at hHigh
      try simp only [] at hHigh
      simp only [Option.some.injEq] at hHigh
      rw [← hHigh]
      constructor
      · change (emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.returned value)) _).state).ffi.ioEvents <+: (emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.returned value)) _).state).ffi.ioEvents
        rw [callFixedContextHOLExact_callEntry_stateAddClock_state context.state calleeLocals
          ((some (.returned value))) postContext extra hclock]
        simp only [emptyLocalsHOLExact_stateAddClock, stateAddClock_ffi]
        exact List.prefix_refl _
      · intro _
        congr 1
        apply PanSemExactEvalContext.ext
        change emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.returned value)) _).state = stateAddClock ((emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.returned value)) _).state)) extra
        rw [callFixedContextHOLExact_callEntry_stateAddClock_state context.state calleeLocals
          ((some (.returned value))) postContext extra hclock]
        simp only [emptyLocalsHOLExact_stateAddClock]
        rfl
  case case27 =>
    rename_i inst context state function arguments values hargs body calleeLocals returnShape
      hlookup hclock entry entryContext postContext value hshape snd hbody fixedContext ih1
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalListHOLExact_stateAddClock] at hHigh
    rw [show evalListHOLExact context.state arguments = some values from hargs] at hHigh
    try simp only [] at hHigh
    rw [show lookupCodeHOLExact context.state.code function values = some (body, calleeLocals, returnShape) from hlookup] at hHigh
    try simp only [] at hHigh
    rw [if_neg (by have hc : context.state.clock ≠ 0 := hclock; omega)] at hHigh
    try simp only [] at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rB cB hbodyH
      have hbodyH' : evalPanSemRecursiveCallContextHOLExact body (ctxAddClock entryContext extra) =
          some (rB, cB) := by
        rw [← eval_context_state body _ (ctxAddClock entryContext extra)]
        · exact hbodyH
        · change callEntryStateHOLExact (stateAddClock context.state extra) calleeLocals = stateAddClock entry extra
          rw [callEntryStateHOLExact_stateAddClock context.state calleeLocals extra hclock]
      have hih1 := ih1 extra (some (.returned value), postContext) (rB, cB) hbody hbodyH'
      obtain ⟨hrB, hcB⟩ := Prod.mk.inj (hih1.2 (by simp))
      cases hrB
      cases hcB
      dsimp only at hHigh
      rw [if_pos hshape] at hHigh
      simp only [Option.some.injEq] at hHigh
      rw [← hHigh]
      constructor
      · simp only [PanSemExactEvalContext.withState_state,
          callFixedContextHOLExact_callEntry_stateAddClock_state context.state calleeLocals
            (some (.returned value)) postContext extra hclock, stateAddClock_ffi]
        exact List.prefix_refl _
      · intro _
        congr 1
        apply PanSemExactEvalContext.ext
        simp only [PanSemExactEvalContext.withState_state,
          callFixedContextHOLExact_callEntry_stateAddClock_state context.state calleeLocals
            (some (.returned value)) postContext extra hclock]
        rfl
  case case28 =>
    rename_i inst context state function arguments values hargs body calleeLocals returnShape
      hlookup hclock entry entryContext postContext value hshape kind name snd hvalid hbody fixedContext ih1
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalListHOLExact_stateAddClock] at hHigh
    rw [show evalListHOLExact context.state arguments = some values from hargs] at hHigh
    try simp only [] at hHigh
    rw [show lookupCodeHOLExact context.state.code function values = some (body, calleeLocals, returnShape) from hlookup] at hHigh
    try simp only [] at hHigh
    rw [if_neg (by have hc : context.state.clock ≠ 0 := hclock; omega)] at hHigh
    try simp only [] at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rB cB hbodyH
      have hbodyH' : evalPanSemRecursiveCallContextHOLExact body (ctxAddClock entryContext extra) =
          some (rB, cB) := by
        rw [← eval_context_state body _ (ctxAddClock entryContext extra)]
        · exact hbodyH
        · change callEntryStateHOLExact (stateAddClock context.state extra) calleeLocals = stateAddClock entry extra
          rw [callEntryStateHOLExact_stateAddClock context.state calleeLocals extra hclock]
      have hih1 := ih1 extra (some (.returned value), postContext) (rB, cB) hbody hbodyH'
      obtain ⟨hrB, hcB⟩ := Prod.mk.inj (hih1.2 (by simp))
      cases hrB
      cases hcB
      dsimp only at hHigh
      rw [if_pos hshape] at hHigh
      rw [if_pos (by simpa only [isValidValueHOLExact_stateAddClock] using hvalid)] at hHigh
      simp only [Option.some.injEq] at hHigh
      rw [← hHigh]
      constructor
      · simp only [PanSemExactEvalContext.withState_state,
          callFixedContextHOLExact_callEntry_stateAddClock_state context.state calleeLocals
            (some (.returned value)) postContext extra hclock, setKvarHOLExact_ffi, stateAddClock_ffi]
        exact List.prefix_refl _
      · intro _
        congr 1
        apply PanSemExactEvalContext.ext
        simp only [PanSemExactEvalContext.withState_state,
          callFixedContextHOLExact_callEntry_stateAddClock_state context.state calleeLocals
            (some (.returned value)) postContext extra hclock]
        cases kind <;> rfl
  case case29 =>
    rename_i inst context state function arguments values hargs body calleeLocals returnShape
      hlookup hclock entry entryContext postContext value hshape kind name snd hvalid hbody fixedContext ih1
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalListHOLExact_stateAddClock] at hHigh
    rw [show evalListHOLExact context.state arguments = some values from hargs] at hHigh
    try simp only [] at hHigh
    rw [show lookupCodeHOLExact context.state.code function values = some (body, calleeLocals, returnShape) from hlookup] at hHigh
    try simp only [] at hHigh
    rw [if_neg (by have hc : context.state.clock ≠ 0 := hclock; omega)] at hHigh
    try simp only [] at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rB cB hbodyH
      have hbodyH' : evalPanSemRecursiveCallContextHOLExact body (ctxAddClock entryContext extra) =
          some (rB, cB) := by
        rw [← eval_context_state body _ (ctxAddClock entryContext extra)]
        · exact hbodyH
        · change callEntryStateHOLExact (stateAddClock context.state extra) calleeLocals = stateAddClock entry extra
          rw [callEntryStateHOLExact_stateAddClock context.state calleeLocals extra hclock]
      have hih1 := ih1 extra (some (.returned value), postContext) (rB, cB) hbody hbodyH'
      obtain ⟨hrB, hcB⟩ := Prod.mk.inj (hih1.2 (by simp))
      cases hrB
      cases hcB
      try simp only [] at hHigh
      rw [if_pos hshape] at hHigh
      try simp only [] at hHigh
      rw [if_neg (by simpa only [isValidValueHOLExact_stateAddClock] using hvalid)] at hHigh
      try simp only [] at hHigh
      rw [callFixedContextHOLExact_callEntry_stateAddClock context.state calleeLocals
        (some (.returned value)) postContext extra hclock] at hHigh
      simp only [Option.some.injEq] at hHigh
      rw [← hHigh]
      exact ⟨List.prefix_refl _, by intro _; rfl⟩
  case case30 =>
    rename_i inst context state info function arguments values hargs body calleeLocals returnShape
      hlookup hclock entry entryContext postContext value hshape hbody fixedContext ih1
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalListHOLExact_stateAddClock] at hHigh
    rw [show evalListHOLExact context.state arguments = some values from hargs] at hHigh
    try simp only [] at hHigh
    rw [show lookupCodeHOLExact context.state.code function values = some (body, calleeLocals, returnShape) from hlookup] at hHigh
    try simp only [] at hHigh
    rw [if_neg (by have hc : context.state.clock ≠ 0 := hclock; omega)] at hHigh
    try simp only [] at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rB cB hbodyH
      have hbodyH' : evalPanSemRecursiveCallContextHOLExact body (ctxAddClock entryContext extra) =
          some (rB, cB) := by
        rw [← eval_context_state body _ (ctxAddClock entryContext extra)]
        · exact hbodyH
        · change callEntryStateHOLExact (stateAddClock context.state extra) calleeLocals = stateAddClock entry extra
          rw [callEntryStateHOLExact_stateAddClock context.state calleeLocals extra hclock]
      have hih1 := ih1 extra (some (.returned value), postContext) (rB, cB) hbody hbodyH'
      obtain ⟨hrB, hcB⟩ := Prod.mk.inj (hih1.2 (by simp))
      cases hrB
      cases hcB
      try simp only [] at hHigh
      rw [if_neg hshape] at hHigh
      try simp only [] at hHigh
      rw [callFixedContextHOLExact_callEntry_stateAddClock context.state calleeLocals
        (some (.returned value)) postContext extra hclock] at hHigh
      simp only [Option.some.injEq] at hHigh
      rw [← hHigh]
      exact ⟨List.prefix_refl _, by intro _; rfl⟩
  case case31 =>
    rename_i inst context state function arguments values hargs body calleeLocals returnShape
      hlookup hclock entry entryContext postContext exceptionId value hbody fixedContext ih1
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalListHOLExact_stateAddClock] at hHigh
    rw [show evalListHOLExact context.state arguments = some values from hargs] at hHigh
    try simp only [] at hHigh
    rw [show lookupCodeHOLExact context.state.code function values = some (body, calleeLocals, returnShape) from hlookup] at hHigh
    try simp only [] at hHigh
    rw [if_neg (by have hc : context.state.clock ≠ 0 := hclock; omega)] at hHigh
    try simp only [] at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rB cB hbodyH
      have hbodyH' : evalPanSemRecursiveCallContextHOLExact body (ctxAddClock entryContext extra) =
          some (rB, cB) := by
        rw [← eval_context_state body _ (ctxAddClock entryContext extra)]
        · exact hbodyH
        · change callEntryStateHOLExact (stateAddClock context.state extra) calleeLocals = stateAddClock entry extra
          rw [callEntryStateHOLExact_stateAddClock context.state calleeLocals extra hclock]
      have hih1 := ih1 extra ((some (.exception exceptionId value)), postContext) (rB, cB) hbody hbodyH'
      obtain ⟨hrB, hcB⟩ := Prod.mk.inj (hih1.2 (by simp))
      cases hrB
      cases hcB
      try simp only [] at hHigh
      simp only [Option.some.injEq] at hHigh
      rw [← hHigh]
      constructor
      · change (emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.exception exceptionId value)) _).state).ffi.ioEvents <+: (emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.exception exceptionId value)) _).state).ffi.ioEvents
        rw [callFixedContextHOLExact_callEntry_stateAddClock_state context.state calleeLocals
          ((some (.exception exceptionId value))) postContext extra hclock]
        simp only [emptyLocalsHOLExact_stateAddClock, stateAddClock_ffi]
        exact List.prefix_refl _
      · intro _
        congr 1
        apply PanSemExactEvalContext.ext
        change emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.exception exceptionId value)) _).state = stateAddClock ((emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.exception exceptionId value)) _).state)) extra
        rw [callFixedContextHOLExact_callEntry_stateAddClock_state context.state calleeLocals
          ((some (.exception exceptionId value))) postContext extra hclock]
        simp only [emptyLocalsHOLExact_stateAddClock]
        rfl
  case case32 =>
    rename_i inst context state function arguments values hargs body calleeLocals returnShape
      hlookup hclock entry entryContext postContext exceptionId value fst hbody fixedContext ih1
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalListHOLExact_stateAddClock] at hHigh
    rw [show evalListHOLExact context.state arguments = some values from hargs] at hHigh
    try simp only [] at hHigh
    rw [show lookupCodeHOLExact context.state.code function values = some (body, calleeLocals, returnShape) from hlookup] at hHigh
    try simp only [] at hHigh
    rw [if_neg (by have hc : context.state.clock ≠ 0 := hclock; omega)] at hHigh
    try simp only [] at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rB cB hbodyH
      have hbodyH' : evalPanSemRecursiveCallContextHOLExact body (ctxAddClock entryContext extra) =
          some (rB, cB) := by
        rw [← eval_context_state body _ (ctxAddClock entryContext extra)]
        · exact hbodyH
        · change callEntryStateHOLExact (stateAddClock context.state extra) calleeLocals = stateAddClock entry extra
          rw [callEntryStateHOLExact_stateAddClock context.state calleeLocals extra hclock]
      have hih1 := ih1 extra ((some (.exception exceptionId value)), postContext) (rB, cB) hbody hbodyH'
      obtain ⟨hrB, hcB⟩ := Prod.mk.inj (hih1.2 (by simp))
      cases hrB
      cases hcB
      try simp only [] at hHigh
      simp only [Option.some.injEq] at hHigh
      rw [← hHigh]
      constructor
      · change (emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.exception exceptionId value)) _).state).ffi.ioEvents <+: (emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.exception exceptionId value)) _).state).ffi.ioEvents
        rw [callFixedContextHOLExact_callEntry_stateAddClock_state context.state calleeLocals
          ((some (.exception exceptionId value))) postContext extra hclock]
        simp only [emptyLocalsHOLExact_stateAddClock, stateAddClock_ffi]
        exact List.prefix_refl _
      · intro _
        congr 1
        apply PanSemExactEvalContext.ext
        change emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.exception exceptionId value)) _).state = stateAddClock ((emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.exception exceptionId value)) _).state)) extra
        rw [callFixedContextHOLExact_callEntry_stateAddClock_state context.state calleeLocals
          ((some (.exception exceptionId value))) postContext extra hclock]
        simp only [emptyLocalsHOLExact_stateAddClock]
        rfl
  case case33 =>
    rename_i inst context state function arguments values hargs body calleeLocals returnShape
      hlookup hclock entry entryContext postContext value fst handlerId handlerVar handlerProgram shape
      hshape hend hbody fixedContext handlerState handlerContext ih2 ih1
    intro extra resultLow resultHigh hLow hHigh
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalListHOLExact_stateAddClock] at hHigh
    rw [show evalListHOLExact context.state arguments = some values from hargs] at hHigh
    try simp only [] at hHigh
    rw [show lookupCodeHOLExact context.state.code function values = some (body, calleeLocals, returnShape) from hlookup] at hHigh
    try simp only [] at hHigh
    rw [if_neg (by have hc : context.state.clock ≠ 0 := hclock; omega)] at hHigh
    try simp only [] at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rB cB hbodyH
      have hbodyH' : evalPanSemRecursiveCallContextHOLExact body (ctxAddClock entryContext extra) =
          some (rB, cB) := by
        rw [← eval_context_state body _ (ctxAddClock entryContext extra)]
        · exact hbodyH
        · change callEntryStateHOLExact (stateAddClock context.state extra) calleeLocals = stateAddClock entry extra
          rw [callEntryStateHOLExact_stateAddClock context.state calleeLocals extra hclock]
      have hih2 := ih2 extra (some (.exception handlerId value), postContext) (rB, cB) hbody hbodyH'
      obtain ⟨hrB, hcB⟩ := Prod.mk.inj (hih2.2 (by simp))
      cases hrB
      cases hcB
      dsimp only at hHigh
      rw [if_pos rfl] at hHigh
      rw [show (stateAddClock context.state extra).eshapes handlerId = some shape from by rw [stateAddClock_eshapes]; exact hend] at hHigh
      try simp only [] at hHigh
      rw [if_pos (by simpa only [isValidValueHOLExact_stateAddClock] using hshape)] at hHigh
      have hhandlerH : evalPanSemRecursiveCallContextHOLExact handlerProgram
          (ctxAddClock handlerContext extra) = some resultHigh := by
        rw [← eval_context_state handlerProgram _ (ctxAddClock handlerContext extra)]
        · exact hHigh
        · simp only [callFixedContextHOLExact_callEntry_stateAddClock context.state calleeLocals
            (some (.exception handlerId value)) postContext extra hclock]
          exact handlerStateHOLExact_stateAddClock context fixedContext handlerVar value extra
      exact ih1 extra resultLow resultHigh hLow hhandlerH
  case case34 =>
    rename_i inst context state function arguments values hargs body calleeLocals returnShape
      hlookup hclock entry entryContext postContext value fst handlerId handlerVar handlerProgram shape
      hinv hend hbody fixedContext ih1
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalListHOLExact_stateAddClock] at hHigh
    rw [show evalListHOLExact context.state arguments = some values from hargs] at hHigh
    try simp only [] at hHigh
    rw [show lookupCodeHOLExact context.state.code function values = some (body, calleeLocals, returnShape) from hlookup] at hHigh
    try simp only [] at hHigh
    rw [if_neg (by have hc : context.state.clock ≠ 0 := hclock; omega)] at hHigh
    try simp only [] at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rB cB hbodyH
      have hbodyH' : evalPanSemRecursiveCallContextHOLExact body (ctxAddClock entryContext extra) =
          some (rB, cB) := by
        rw [← eval_context_state body _ (ctxAddClock entryContext extra)]
        · exact hbodyH
        · change callEntryStateHOLExact (stateAddClock context.state extra) calleeLocals = stateAddClock entry extra
          rw [callEntryStateHOLExact_stateAddClock context.state calleeLocals extra hclock]
      have hih1 := ih1 extra (some (.exception handlerId value), postContext) (rB, cB) hbody hbodyH'
      obtain ⟨hrB, hcB⟩ := Prod.mk.inj (hih1.2 (by simp))
      cases hrB
      cases hcB
      dsimp only at hHigh
      rw [if_pos rfl] at hHigh
      rw [show (stateAddClock context.state extra).eshapes handlerId = some shape from by rw [stateAddClock_eshapes]; exact hend] at hHigh
      try simp only [] at hHigh
      rw [if_neg (by simpa only [isValidValueHOLExact_stateAddClock] using hinv)] at hHigh
      rw [callFixedContextHOLExact_callEntry_stateAddClock context.state calleeLocals
        (some (.exception handlerId value)) postContext extra hclock] at hHigh
      simp only [Option.some.injEq] at hHigh
      rw [← hHigh]
      exact ⟨List.prefix_refl _, by intro _; rfl⟩
  case case35 =>
    rename_i inst context state function arguments values hargs body calleeLocals returnShape
      hlookup hclock entry entryContext postContext value fst handlerId handlerVar handlerProgram
      hnone hbody fixedContext ih1
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalListHOLExact_stateAddClock] at hHigh
    rw [show evalListHOLExact context.state arguments = some values from hargs] at hHigh
    try simp only [] at hHigh
    rw [show lookupCodeHOLExact context.state.code function values = some (body, calleeLocals, returnShape) from hlookup] at hHigh
    try simp only [] at hHigh
    rw [if_neg (by have hc : context.state.clock ≠ 0 := hclock; omega)] at hHigh
    try simp only [] at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rB cB hbodyH
      have hbodyH' : evalPanSemRecursiveCallContextHOLExact body (ctxAddClock entryContext extra) =
          some (rB, cB) := by
        rw [← eval_context_state body _ (ctxAddClock entryContext extra)]
        · exact hbodyH
        · change callEntryStateHOLExact (stateAddClock context.state extra) calleeLocals = stateAddClock entry extra
          rw [callEntryStateHOLExact_stateAddClock context.state calleeLocals extra hclock]
      have hih1 := ih1 extra (some (.exception handlerId value), postContext) (rB, cB) hbody hbodyH'
      obtain ⟨hrB, hcB⟩ := Prod.mk.inj (hih1.2 (by simp))
      cases hrB
      cases hcB
      dsimp only at hHigh
      rw [if_pos rfl] at hHigh
      rw [show (stateAddClock context.state extra).eshapes handlerId = none from by rw [stateAddClock_eshapes]; exact hnone] at hHigh
      try dsimp only at hHigh
      rw [callFixedContextHOLExact_callEntry_stateAddClock context.state calleeLocals
        (some (.exception handlerId value)) postContext extra hclock] at hHigh
      simp only [Option.some.injEq] at hHigh
      rw [← hHigh]
      exact ⟨List.prefix_refl _, by intro _; rfl⟩
  case case36 =>
    rename_i inst context state function arguments values hargs body calleeLocals returnShape
      hlookup hclock entry entryContext postContext exceptionId value fst handlerId handlerVar handlerProgram hne hbody fixedContext ih1
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalListHOLExact_stateAddClock] at hHigh
    rw [show evalListHOLExact context.state arguments = some values from hargs] at hHigh
    try simp only [] at hHigh
    rw [show lookupCodeHOLExact context.state.code function values = some (body, calleeLocals, returnShape) from hlookup] at hHigh
    try simp only [] at hHigh
    rw [if_neg (by have hc : context.state.clock ≠ 0 := hclock; omega)] at hHigh
    try simp only [] at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rB cB hbodyH
      have hbodyH' : evalPanSemRecursiveCallContextHOLExact body (ctxAddClock entryContext extra) =
          some (rB, cB) := by
        rw [← eval_context_state body _ (ctxAddClock entryContext extra)]
        · exact hbodyH
        · change callEntryStateHOLExact (stateAddClock context.state extra) calleeLocals = stateAddClock entry extra
          rw [callEntryStateHOLExact_stateAddClock context.state calleeLocals extra hclock]
      have hih1 := ih1 extra ((some (.exception exceptionId value)), postContext) (rB, cB) hbody hbodyH'
      obtain ⟨hrB, hcB⟩ := Prod.mk.inj (hih1.2 (by simp))
      cases hrB
      cases hcB
      try simp only [] at hHigh
      rw [if_neg hne] at hHigh
      try simp only [] at hHigh
      simp only [Option.some.injEq] at hHigh
      rw [← hHigh]
      constructor
      · change (emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.exception exceptionId value)) _).state).ffi.ioEvents <+: (emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.exception exceptionId value)) _).state).ffi.ioEvents
        rw [callFixedContextHOLExact_callEntry_stateAddClock_state context.state calleeLocals
          ((some (.exception exceptionId value))) postContext extra hclock]
        simp only [emptyLocalsHOLExact_stateAddClock, stateAddClock_ffi]
        exact List.prefix_refl _
      · intro _
        congr 1
        apply PanSemExactEvalContext.ext
        change emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.exception exceptionId value)) _).state = stateAddClock ((emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.exception exceptionId value)) _).state)) extra
        rw [callFixedContextHOLExact_callEntry_stateAddClock_state context.state calleeLocals
          ((some (.exception exceptionId value))) postContext extra hclock]
        simp only [emptyLocalsHOLExact_stateAddClock]
        rfl
  case case37 =>
    rename_i inst context state info function arguments values hargs body calleeLocals returnShape
      hlookup hclock entry entryContext postContext other hbrk hcont hret hexc hbody fixedContext ih1
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalListHOLExact_stateAddClock] at hHigh
    rw [show evalListHOLExact context.state arguments = some values from hargs] at hHigh
    try simp only [] at hHigh
    rw [show lookupCodeHOLExact context.state.code function values = some (body, calleeLocals, returnShape) from hlookup] at hHigh
    try simp only [] at hHigh
    rw [if_neg (by have hc : context.state.clock ≠ 0 := hclock; omega)] at hHigh
    try simp only [] at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rB cB hbodyH
      have hbodyH' : evalPanSemRecursiveCallContextHOLExact body (ctxAddClock entryContext extra) =
          some (rB, cB) := by
        rw [← eval_context_state body _ (ctxAddClock entryContext extra)]
        · exact hbodyH
        · change callEntryStateHOLExact (stateAddClock context.state extra) calleeLocals = stateAddClock entry extra
          rw [callEntryStateHOLExact_stateAddClock context.state calleeLocals extra hclock]
      have hih1 := ih1 extra (some other, postContext) (rB, cB) hbody hbodyH'
      have hpref : postContext.state.ffi.ioEvents <+: cB.state.ffi.ioEvents := hih1.1
      by_cases hto : (some other : Option (PanSemResultExact width)) = some .timeOut
      · constructor
        · change postContext.state.ffi.ioEvents <+: resultHigh.2.state.ffi.ioEvents
          cases rB with
          | none =>
              rw [← Option.some.inj hHigh]
              simp only [callFixedContextHOLExact_state_ffi]
              exact hpref
          | some br =>
              cases br with
              | error =>
                  rw [← Option.some.inj hHigh]
                  simp only [PanSemExactEvalContext.withState_state, callFixedContextHOLExact_state_ffi,
                    emptyLocalsHOLExact]
                  exact hpref
              | timeOut =>
                  rw [← Option.some.inj hHigh]
                  simp only [PanSemExactEvalContext.withState_state, callFixedContextHOLExact_state_ffi,
                    emptyLocalsHOLExact]
                  exact hpref
              | finalFfi e =>
                  rw [← Option.some.inj hHigh]
                  simp only [PanSemExactEvalContext.withState_state, callFixedContextHOLExact_state_ffi,
                    emptyLocalsHOLExact]
                  exact hpref
              | «break» =>
                  rw [← Option.some.inj hHigh]
                  simp only [callFixedContextHOLExact_state_ffi]
                  exact hpref
              | «continue» =>
                  rw [← Option.some.inj hHigh]
                  simp only [callFixedContextHOLExact_state_ffi]
                  exact hpref
              | returned v =>
                  try (split at hHigh) <;> try (split at hHigh) <;> try (split at hHigh) <;>
                  try (split at hHigh) <;> try (split at hHigh)
                  all_goals
                    (first
                     | (rw [← Option.some.inj hHigh]
                        simp only [PanSemExactEvalContext.withState_state, callFixedContextHOLExact_state_ffi,
                          emptyLocalsHOLExact, setKvarHOLExact_ffi]
                        exact hpref)
                     | (simp_all))
              | exception e v =>
                  try (split at hHigh) <;> try (split at hHigh) <;> try (split at hHigh) <;>
                  try (split at hHigh) <;> try (split at hHigh)
                  all_goals
                    (first
                     | (rw [← Option.some.inj hHigh]
                        simp only [PanSemExactEvalContext.withState_state, callFixedContextHOLExact_state_ffi,
                          emptyLocalsHOLExact]
                        exact hpref)
                     | (have hh : cB.state.ffi.ioEvents <+: resultHigh.2.state.ffi.ioEvents := by
                          simpa only [PanSemExactEvalContext.withState_state, handlerStateHOLExact,
                            setVarHOLExact, callFixedContextHOLExact_state_ffi]
                            using (evalPanSemRecursiveCallContextHOLExact_ioEvents_prefix _ _ resultHigh hHigh)
                        exact hpref.trans hh)
                     | (simp_all))
        · intro hne; exact absurd hto hne
      · obtain ⟨hrB, hcB⟩ := Prod.mk.inj (hih1.2 hto)
        cases hrB
        cases hcB
        cases other with
        | «break» => exfalso; exact hbrk rfl
        | «continue» => exfalso; exact hcont rfl
        | returned v => exfalso; exact hret v rfl
        | exception e v => exfalso; exact hexc e v rfl
        | timeOut => exfalso; exact absurd rfl hto
        | error =>
            dsimp only at hHigh
            simp only [Option.some.injEq] at hHigh
            rw [← hHigh]
            constructor
            · change (emptyLocalsHOLExact (callFixedContextHOLExact _ (some .error) _).state).ffi.ioEvents <+: (emptyLocalsHOLExact (callFixedContextHOLExact _ (some .error) _).state).ffi.ioEvents
              rw [callFixedContextHOLExact_callEntry_stateAddClock_state context.state calleeLocals
                (some .error) postContext extra hclock]
              simp only [emptyLocalsHOLExact_stateAddClock, stateAddClock_ffi]
              exact List.prefix_refl _
            · intro _
              congr 1
              apply PanSemExactEvalContext.ext
              change emptyLocalsHOLExact (callFixedContextHOLExact _ (some .error) _).state = stateAddClock ((emptyLocalsHOLExact (callFixedContextHOLExact _ (some .error) _).state)) extra
              rw [callFixedContextHOLExact_callEntry_stateAddClock_state context.state calleeLocals
                (some .error) postContext extra hclock]
              simp only [emptyLocalsHOLExact_stateAddClock]
              rfl
        | finalFfi e =>
            dsimp only at hHigh
            simp only [Option.some.injEq] at hHigh
            rw [← hHigh]
            constructor
            · change (emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.finalFfi e)) _).state).ffi.ioEvents <+: (emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.finalFfi e)) _).state).ffi.ioEvents
              rw [callFixedContextHOLExact_callEntry_stateAddClock_state context.state calleeLocals
                (some (.finalFfi e)) postContext extra hclock]
              simp only [emptyLocalsHOLExact_stateAddClock, stateAddClock_ffi]
              exact List.prefix_refl _
            · intro _
              congr 1
              apply PanSemExactEvalContext.ext
              change emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.finalFfi e)) _).state = stateAddClock ((emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.finalFfi e)) _).state)) extra
              rw [callFixedContextHOLExact_callEntry_stateAddClock_state context.state calleeLocals
                (some (.finalFfi e)) postContext extra hclock]
              simp only [emptyLocalsHOLExact_stateAddClock]
              rfl
  case case40 =>
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    constructor
    · have hprefix := evalPanSemRecursiveCallContextHOLExact_ioEvents_prefix
          _ _ resultHigh hHigh
      exact hprefix
    · intro hne; exact absurd rfl hne
  case case42 =>
    rename_i inst context state resultName shape function arguments continuation values hargs
      body calleeLocals returnShape hlookup hclock entry entryContext postContext hbody fixedContext ih1
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalListHOLExact_stateAddClock] at hHigh
    rw [show evalListHOLExact context.state arguments = some values from hargs] at hHigh
    try simp only [] at hHigh
    rw [show lookupCodeHOLExact context.state.code function values = some (body, calleeLocals, returnShape) from hlookup] at hHigh
    try simp only [] at hHigh
    rw [if_neg (by have hc : context.state.clock ≠ 0 := hclock; omega)] at hHigh
    try simp only [] at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rB cB hbodyH
      have hbodyH' : evalPanSemRecursiveCallContextHOLExact body (ctxAddClock entryContext extra) =
          some (rB, cB) := by
        rw [← eval_context_state body _ (ctxAddClock entryContext extra)]
        · exact hbodyH
        · change callEntryStateHOLExact (stateAddClock context.state extra) calleeLocals = stateAddClock entry extra
          rw [callEntryStateHOLExact_stateAddClock context.state calleeLocals extra hclock]
      have hih1 := ih1 extra (none, postContext) (rB, cB) hbody hbodyH'
      obtain ⟨hrB, hcB⟩ := Prod.mk.inj (hih1.2 (by simp))
      cases hrB
      cases hcB
      dsimp only at hHigh
      rw [callFixedContextHOLExact_callEntry_stateAddClock context.state calleeLocals
        (none) postContext extra hclock] at hHigh
      simp only [Option.some.injEq] at hHigh
      rw [← hHigh]
      exact ⟨List.prefix_refl _, by intro _; rfl⟩
  case case43 =>
    rename_i inst context state resultName shape function arguments continuation values hargs
      body calleeLocals returnShape hlookup hclock entry entryContext postContext hbody fixedContext ih1
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalListHOLExact_stateAddClock] at hHigh
    rw [show evalListHOLExact context.state arguments = some values from hargs] at hHigh
    try simp only [] at hHigh
    rw [show lookupCodeHOLExact context.state.code function values = some (body, calleeLocals, returnShape) from hlookup] at hHigh
    try simp only [] at hHigh
    rw [if_neg (by have hc : context.state.clock ≠ 0 := hclock; omega)] at hHigh
    try simp only [] at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rB cB hbodyH
      have hbodyH' : evalPanSemRecursiveCallContextHOLExact body (ctxAddClock entryContext extra) =
          some (rB, cB) := by
        rw [← eval_context_state body _ (ctxAddClock entryContext extra)]
        · exact hbodyH
        · change callEntryStateHOLExact (stateAddClock context.state extra) calleeLocals = stateAddClock entry extra
          rw [callEntryStateHOLExact_stateAddClock context.state calleeLocals extra hclock]
      have hih1 := ih1 extra (some .break, postContext) (rB, cB) hbody hbodyH'
      obtain ⟨hrB, hcB⟩ := Prod.mk.inj (hih1.2 (by simp))
      cases hrB
      cases hcB
      dsimp only at hHigh
      rw [callFixedContextHOLExact_callEntry_stateAddClock context.state calleeLocals
        (some .break) postContext extra hclock] at hHigh
      simp only [Option.some.injEq] at hHigh
      rw [← hHigh]
      exact ⟨List.prefix_refl _, by intro _; rfl⟩
  case case44 =>
    rename_i inst context state resultName shape function arguments continuation values hargs
      body calleeLocals returnShape hlookup hclock entry entryContext postContext hbody fixedContext ih1
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalListHOLExact_stateAddClock] at hHigh
    rw [show evalListHOLExact context.state arguments = some values from hargs] at hHigh
    try simp only [] at hHigh
    rw [show lookupCodeHOLExact context.state.code function values = some (body, calleeLocals, returnShape) from hlookup] at hHigh
    try simp only [] at hHigh
    rw [if_neg (by have hc : context.state.clock ≠ 0 := hclock; omega)] at hHigh
    try simp only [] at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rB cB hbodyH
      have hbodyH' : evalPanSemRecursiveCallContextHOLExact body (ctxAddClock entryContext extra) =
          some (rB, cB) := by
        rw [← eval_context_state body _ (ctxAddClock entryContext extra)]
        · exact hbodyH
        · change callEntryStateHOLExact (stateAddClock context.state extra) calleeLocals = stateAddClock entry extra
          rw [callEntryStateHOLExact_stateAddClock context.state calleeLocals extra hclock]
      have hih1 := ih1 extra (some .continue, postContext) (rB, cB) hbody hbodyH'
      obtain ⟨hrB, hcB⟩ := Prod.mk.inj (hih1.2 (by simp))
      cases hrB
      cases hcB
      dsimp only at hHigh
      rw [callFixedContextHOLExact_callEntry_stateAddClock context.state calleeLocals
        (some .continue) postContext extra hclock] at hHigh
      simp only [Option.some.injEq] at hHigh
      rw [← hHigh]
      exact ⟨List.prefix_refl _, by intro _; rfl⟩
  case case46 =>
    rename_i inst context state resultName shape function arguments continuation values hargs
      body calleeLocals returnShape hlookup hclock entry entryContext postContextBody value hshape
      result postContext restored hbody fixedContext continuationContext hcont ih2 ih1
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalListHOLExact_stateAddClock] at hHigh
    rw [show evalListHOLExact context.state arguments = some values from hargs] at hHigh
    try simp only [] at hHigh
    rw [show lookupCodeHOLExact context.state.code function values = some (body, calleeLocals, returnShape) from hlookup] at hHigh
    try simp only [] at hHigh
    rw [if_neg (by have hc : context.state.clock ≠ 0 := hclock; omega)] at hHigh
    try simp only [] at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rB cB hbodyH
      have hbodyH' : evalPanSemRecursiveCallContextHOLExact body (ctxAddClock entryContext extra) =
          some (rB, cB) := by
        rw [← eval_context_state body _ (ctxAddClock entryContext extra)]
        · exact hbodyH
        · change callEntryStateHOLExact (stateAddClock context.state extra) calleeLocals = stateAddClock entry extra
          rw [callEntryStateHOLExact_stateAddClock context.state calleeLocals extra hclock]
      have hih2 := ih2 extra (some (.returned value), postContextBody) (rB, cB) hbody hbodyH'
      obtain ⟨hrB, hcB⟩ := Prod.mk.inj (hih2.2 (by simp))
      cases hrB
      cases hcB
      dsimp only at hHigh
      rw [if_pos hshape] at hHigh
      split at hHigh
      · simp at hHigh
      · rename_i rC cC hcontH
        simp only [callFixedContextHOLExact_callEntry_stateAddClock context.state calleeLocals
          (some (.returned value)) postContextBody extra hclock] at hcontH
        have hcontH' : evalPanSemRecursiveCallContextHOLExact continuation
            (ctxAddClock continuationContext extra) = some (rC, cC) := by
          rw [← eval_context_state continuation _ (ctxAddClock continuationContext extra)]
          · exact hcontH
          · exact congrArg PanSemExactEvalContext.state
              (callContinuationContextHOLExact_stateAddClock context fixedContext resultName value extra)
        have hih1 := ih1 extra (result, postContext) (rC, cC) hcont hcontH'
        have hpref : postContext.state.ffi.ioEvents <+: cC.state.ffi.ioEvents := hih1.1
        by_cases hto : result = some PanSemResultExact.timeOut
        · constructor
          · change postContext.state.ffi.ioEvents <+: resultHigh.2.state.ffi.ioEvents
            simp only [Option.some.injEq] at hHigh
            rw [← hHigh]
            first
             | exact hpref
             | simpa only [PanSemExactEvalContext.withState_state] using hpref
          · intro hne; exact absurd hto hne
        · obtain ⟨hrC, hcC⟩ := Prod.mk.inj (hih1.2 hto)
          cases hrC
          cases hcC
          dsimp only at hHigh
          simp only [Option.some.injEq] at hHigh
          rw [← hHigh]
          exact ⟨List.prefix_refl _, by intro _; rfl⟩
  case case47 =>
    rename_i inst context state resultName shape function arguments continuation values hargs
      body calleeLocals returnShape hlookup hclock entry entryContext postContext value hshape hbody
      fixedContext ih1
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalListHOLExact_stateAddClock] at hHigh
    rw [show evalListHOLExact context.state arguments = some values from hargs] at hHigh
    try simp only [] at hHigh
    rw [show lookupCodeHOLExact context.state.code function values = some (body, calleeLocals, returnShape) from hlookup] at hHigh
    try simp only [] at hHigh
    rw [if_neg (by have hc : context.state.clock ≠ 0 := hclock; omega)] at hHigh
    try simp only [] at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rB cB hbodyH
      have hbodyH' : evalPanSemRecursiveCallContextHOLExact body (ctxAddClock entryContext extra) =
          some (rB, cB) := by
        rw [← eval_context_state body _ (ctxAddClock entryContext extra)]
        · exact hbodyH
        · change callEntryStateHOLExact (stateAddClock context.state extra) calleeLocals = stateAddClock entry extra
          rw [callEntryStateHOLExact_stateAddClock context.state calleeLocals extra hclock]
      have hih1 := ih1 extra (some (.returned value), postContext) (rB, cB) hbody hbodyH'
      obtain ⟨hrB, hcB⟩ := Prod.mk.inj (hih1.2 (by simp))
      cases hrB
      cases hcB
      dsimp only at hHigh
      rw [if_neg hshape] at hHigh
      rw [callFixedContextHOLExact_callEntry_stateAddClock context.state calleeLocals
        (some (.returned value)) postContext extra hclock] at hHigh
      simp only [Option.some.injEq] at hHigh
      rw [← hHigh]
      exact ⟨List.prefix_refl _, by intro _; rfl⟩
  case case48 =>
    rename_i inst context state resultName shape function arguments continuation values hargs
      body calleeLocals returnShape hlookup hclock entry entryContext postContext other
      hbrk hcont hret hbody fixedContext ih1
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalListHOLExact_stateAddClock] at hHigh
    rw [show evalListHOLExact context.state arguments = some values from hargs] at hHigh
    try simp only [] at hHigh
    rw [show lookupCodeHOLExact context.state.code function values = some (body, calleeLocals, returnShape) from hlookup] at hHigh
    try simp only [] at hHigh
    rw [if_neg (by have hc : context.state.clock ≠ 0 := hclock; omega)] at hHigh
    try simp only [] at hHigh
    split at hHigh
    · simp at hHigh
    · rename_i rB cB hbodyH
      have hbodyH' : evalPanSemRecursiveCallContextHOLExact body (ctxAddClock entryContext extra) =
          some (rB, cB) := by
        rw [← eval_context_state body _ (ctxAddClock entryContext extra)]
        · exact hbodyH
        · change callEntryStateHOLExact (stateAddClock context.state extra) calleeLocals = stateAddClock entry extra
          rw [callEntryStateHOLExact_stateAddClock context.state calleeLocals extra hclock]
      have hih1 := ih1 extra (some other, postContext) (rB, cB) hbody hbodyH'
      have hpref : postContext.state.ffi.ioEvents <+: cB.state.ffi.ioEvents := hih1.1
      by_cases hto : (some other : Option (PanSemResultExact width)) = some .timeOut
      · constructor
        · change postContext.state.ffi.ioEvents <+: resultHigh.2.state.ffi.ioEvents
          cases rB with
          | none =>
              rw [← Option.some.inj hHigh]
              simp only [callFixedContextHOLExact_state_ffi]
              exact hpref
          | some br =>
              cases br with
              | error =>
                  rw [← Option.some.inj hHigh]
                  simp only [PanSemExactEvalContext.withState_state, callFixedContextHOLExact_state_ffi,
                    emptyLocalsHOLExact]
                  exact hpref
              | timeOut =>
                  rw [← Option.some.inj hHigh]
                  simp only [PanSemExactEvalContext.withState_state, callFixedContextHOLExact_state_ffi,
                    emptyLocalsHOLExact]
                  exact hpref
              | finalFfi e =>
                  rw [← Option.some.inj hHigh]
                  simp only [PanSemExactEvalContext.withState_state, callFixedContextHOLExact_state_ffi,
                    emptyLocalsHOLExact]
                  exact hpref
              | «break» =>
                  rw [← Option.some.inj hHigh]
                  simp only [callFixedContextHOLExact_state_ffi]
                  exact hpref
              | «continue» =>
                  rw [← Option.some.inj hHigh]
                  simp only [callFixedContextHOLExact_state_ffi]
                  exact hpref
              | exception e v =>
                  rw [← Option.some.inj hHigh]
                  simp only [PanSemExactEvalContext.withState_state, callFixedContextHOLExact_state_ffi,
                    emptyLocalsHOLExact]
                  exact hpref
              | returned v =>
                  try (split at hHigh) <;> try (split at hHigh) <;> try (split at hHigh) <;>
                  try (split at hHigh) <;> try (split at hHigh)
                  all_goals
                    (first
                     | (rw [← Option.some.inj hHigh]
                        simp only [PanSemExactEvalContext.withState_state, callFixedContextHOLExact_state_ffi,
                          emptyLocalsHOLExact]
                        exact hpref)
                     | (rw [← Option.some.inj hHigh]
                        simp only [PanSemExactEvalContext.withState_state]
                        exact hpref.trans
                          (evalPanSemRecursiveCallContextHOLExact_ioEvents_prefix _ _ _ (by assumption)))
                     | (simp_all))
        · intro hne; exact absurd hto hne
      · obtain ⟨hrB, hcB⟩ := Prod.mk.inj (hih1.2 hto)
        cases hrB
        cases hcB
        cases other with
        | «break» => exfalso; exact hbrk rfl
        | «continue» => exfalso; exact hcont rfl
        | returned v => exfalso; exact hret v rfl
        | timeOut => exfalso; exact absurd rfl hto
        | error =>
            dsimp only at hHigh
            simp only [Option.some.injEq] at hHigh
            rw [← hHigh]
            constructor
            · change (emptyLocalsHOLExact (callFixedContextHOLExact _ (some .error) _).state).ffi.ioEvents <+: (emptyLocalsHOLExact (callFixedContextHOLExact _ (some .error) _).state).ffi.ioEvents
              rw [callFixedContextHOLExact_callEntry_stateAddClock_state context.state calleeLocals
                (some .error) postContext extra hclock]
              simp only [emptyLocalsHOLExact_stateAddClock, stateAddClock_ffi]
              exact List.prefix_refl _
            · intro _
              congr 1
              apply PanSemExactEvalContext.ext
              change emptyLocalsHOLExact (callFixedContextHOLExact _ (some .error) _).state = stateAddClock ((emptyLocalsHOLExact (callFixedContextHOLExact _ (some .error) _).state)) extra
              rw [callFixedContextHOLExact_callEntry_stateAddClock_state context.state calleeLocals
                (some .error) postContext extra hclock]
              simp only [emptyLocalsHOLExact_stateAddClock]
              rfl
        | exception e v =>
            dsimp only at hHigh
            simp only [Option.some.injEq] at hHigh
            rw [← hHigh]
            constructor
            · change (emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.exception e v)) _).state).ffi.ioEvents <+: (emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.exception e v)) _).state).ffi.ioEvents
              rw [callFixedContextHOLExact_callEntry_stateAddClock_state context.state calleeLocals
                (some (.exception e v)) postContext extra hclock]
              simp only [emptyLocalsHOLExact_stateAddClock, stateAddClock_ffi]
              exact List.prefix_refl _
            · intro _
              congr 1
              apply PanSemExactEvalContext.ext
              change emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.exception e v)) _).state = stateAddClock ((emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.exception e v)) _).state)) extra
              rw [callFixedContextHOLExact_callEntry_stateAddClock_state context.state calleeLocals
                (some (.exception e v)) postContext extra hclock]
              simp only [emptyLocalsHOLExact_stateAddClock]
              rfl
        | finalFfi e =>
            dsimp only at hHigh
            simp only [Option.some.injEq] at hHigh
            rw [← hHigh]
            constructor
            · change (emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.finalFfi e)) _).state).ffi.ioEvents <+: (emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.finalFfi e)) _).state).ffi.ioEvents
              rw [callFixedContextHOLExact_callEntry_stateAddClock_state context.state calleeLocals
                (some (.finalFfi e)) postContext extra hclock]
              simp only [emptyLocalsHOLExact_stateAddClock, stateAddClock_ffi]
              exact List.prefix_refl _
            · intro _
              congr 1
              apply PanSemExactEvalContext.ext
              change emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.finalFfi e)) _).state = stateAddClock ((emptyLocalsHOLExact (callFixedContextHOLExact _ (some (.finalFfi e)) _).state)) extra
              rw [callFixedContextHOLExact_callEntry_stateAddClock_state context.state calleeLocals
                (some (.finalFfi e)) postContext extra hclock]
              simp only [emptyLocalsHOLExact_stateAddClock]
              rfl
  case case49 =>
    rename_i inst context state kind name source output hmem hshared
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [assignStepHOLExact_stateAddClock] at hHigh
    simp only [Option.some.injEq] at hHigh
    subst resultHigh
    constructor
    · simp only [PanSemExactEvalContext.withState_state, stateAddClock_ffi]
      exact List.prefix_refl _
    · intro _
      first
       | rfl
       | (apply PanSemExactEvalContext.ext
          simp only [PanSemExactEvalContext.withState_state, ctxAddClock_state])
  case case50 =>
    rename_i inst context state name operator arguments output hmem hshared
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [primitiveStepHOLExact_stateAddClock] at hHigh
    simp only [Option.some.injEq] at hHigh
    subst resultHigh
    constructor
    · simp only [PanSemExactEvalContext.withState_state, stateAddClock_ffi]
      exact List.prefix_refl _
    · intro _
      first
       | rfl
       | (apply PanSemExactEvalContext.ext
          simp only [PanSemExactEvalContext.withState_state, ctxAddClock_state])
  case case51 =>
    rename_i inst context state address value output hmem hshared
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [storeStepHOLExact_stateAddClock] at hHigh
    simp only [Option.some.injEq] at hHigh
    subst resultHigh
    constructor
    · simp only [PanSemExactEvalContext.withState_state, stateAddClock_ffi]
      exact List.prefix_refl _
    · intro _
      first
       | rfl
       | (apply PanSemExactEvalContext.ext
          simp only [PanSemExactEvalContext.withState_state, ctxAddClock_state])
  case case52 =>
    rename_i inst context state address value output hmem hshared
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [store32StepHOLExact_stateAddClock] at hHigh
    simp only [Option.some.injEq] at hHigh
    subst resultHigh
    constructor
    · simp only [PanSemExactEvalContext.withState_state, stateAddClock_ffi]
      exact List.prefix_refl _
    · intro _
      first
       | rfl
       | (apply PanSemExactEvalContext.ext
          simp only [PanSemExactEvalContext.withState_state, ctxAddClock_state])
  case case53 =>
    rename_i inst context state address value output hmem hshared
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [storeByteStepHOLExact_stateAddClock] at hHigh
    simp only [Option.some.injEq] at hHigh
    subst resultHigh
    constructor
    · simp only [PanSemExactEvalContext.withState_state, stateAddClock_ffi]
      exact List.prefix_refl _
    · intro _
      first
       | rfl
       | (apply PanSemExactEvalContext.ext
          simp only [PanSemExactEvalContext.withState_state, ctxAddClock_state])
  case case54 =>
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [Option.some.injEq] at hHigh
    rw [← hHigh]
    exact ⟨List.prefix_refl _, by intro _; rfl⟩
  case case55 =>
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [Option.some.injEq] at hHigh
    rw [← hHigh]
    exact ⟨List.prefix_refl _, by intro _; rfl⟩
  case case56 =>
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [Option.some.injEq] at hHigh
    rw [← hHigh]
    exact ⟨List.prefix_refl _, by intro _; rfl⟩
  case case58 =>
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalHOLExact_stateAddClock] at hHigh
    simp_all (config := { zetaDelta := true })
    subst resultHigh
    constructor
    · simp only [PanSemExactEvalContext.withState_state, stateAddClock_ffi]
      exact List.prefix_refl _
    · first
       | rfl
       | (congr 1
          apply PanSemExactEvalContext.ext
          simp only [PanSemExactEvalContext.withState_state, ctxAddClock_state])
  case case59 =>
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp_all (config := { zetaDelta := true })
    rw [if_neg (by omega)] at hHigh
    simp only [Option.some.injEq] at hHigh
    subst resultHigh
    constructor
    · try simp only []
      exact List.prefix_refl _
    · first
       | rfl
       | (congr 1
          apply PanSemExactEvalContext.ext
          simp only [PanSemExactEvalContext.withState_state, ctxAddClock_state])
  case case62 =>
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [evalHOLExact_stateAddClock] at hHigh
    simp_all (config := { zetaDelta := true })
    subst resultHigh
    constructor
    · simp only [PanSemExactEvalContext.withState_state, stateAddClock_ffi]
      exact List.prefix_refl _
    · first
       | rfl
       | (congr 1
          apply PanSemExactEvalContext.ext
          simp only [PanSemExactEvalContext.withState_state, ctxAddClock_state])
  case case63 =>
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp_all (config := { zetaDelta := true })
    rw [if_neg (by omega)] at hHigh
    simp only [Option.some.injEq] at hHigh
    subst resultHigh
    constructor
    · try simp only []
      exact List.prefix_refl _
    · first
       | rfl
       | (congr 1
          apply PanSemExactEvalContext.ext
          simp only [PanSemExactEvalContext.withState_state, ctxAddClock_state])
  case case65 =>
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    constructor
    · have hprefix := evalPanSemRecursiveCallContextHOLExact_ioEvents_prefix
          _ _ resultHigh hHigh
      exact hprefix
    · intro hne; exact absurd rfl hne
  case case66 =>
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp_all (config := { zetaDelta := true })
    subst resultHigh
    constructor
    · try simp only []
      exact List.prefix_refl _
    · first
       | rfl
       | (congr 1
          apply PanSemExactEvalContext.ext
          change decClockHOLExact (stateAddClock _ extra) = stateAddClock (decClockHOLExact _) extra
          exact decClockHOLExact_stateAddClock _ extra (by omega))
  case case67 =>
    rename_i inst context state function configuration configurationLength array arrayLength
      evalExpression output hmem hshared
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [extCallStepHOLExact_stateAddClock] at hHigh
    simp only [Option.some.injEq] at hHigh
    subst resultHigh
    constructor
    · simp only [PanSemExactEvalContext.withState_state, stateAddClock_ffi]
      exact List.prefix_refl _
    · intro _
      first
       | rfl
       | (apply PanSemExactEvalContext.ext
          simp only [PanSemExactEvalContext.withState_state, ctxAddClock_state])
  case case68 =>
    rename_i inst context state size kind name address evalExpression output hdomains
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [shMemLoadClauseHOLExact_stateAddClock] at hHigh
    simp only [Option.some.injEq] at hHigh
    subst resultHigh
    constructor
    · simp only [PanSemExactEvalContext.withState_state, stateAddClock_ffi]
      exact List.prefix_refl _
    · intro _
      first
       | rfl
       | (apply PanSemExactEvalContext.ext
          simp only [PanSemExactEvalContext.withState_state, ctxAddClock_state])
  case case69 =>
    rename_i inst context state size address value evalExpression output hdomains
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [shMemStoreClauseHOLExact_stateAddClock] at hHigh
    simp only [Option.some.injEq] at hHigh
    subst resultHigh
    constructor
    · simp only [PanSemExactEvalContext.withState_state, stateAddClock_ffi]
      exact List.prefix_refl _
    · intro _
      first
       | rfl
       | (apply PanSemExactEvalContext.ext
          simp only [PanSemExactEvalContext.withState_state, ctxAddClock_state])
  case case70 =>
    intro extra resultLow resultHigh hLow hHigh
    cases hLow
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def] at hHigh
    dsimp only at hHigh
    simp only [Option.some.injEq] at hHigh
    rw [← hHigh]
    exact ⟨List.prefix_refl _, by intro _; rfl⟩
  all_goals closeLeaf

/-! ## Clock-increase event-trace prefix (bead flapjack-tu4j)

The Lean analogue of HOL `panPropsScript.sml:881
evaluate_add_clock_io_events_mono`: running the exact recursive panSem
evaluator at a larger clock can only add FFI I/O events, so the
lower-clock run's `ffi.ioEvents` is a list prefix of the higher-clock
run's.  Flapjack-specific infrastructure; no `@[hol]` tag. -/

/-- Given that both the low-clock and the shifted-clock runs terminate at
the given outputs, the low run's `ffi.ioEvents` is a list prefix of the
high run's. -/
theorem evalPanSemRecursiveCallContextHOLExact_add_clock_ioEvents_prefix
    {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) (context : PanSemExactEvalContext width σ) (extra : Nat)
    (resultLow resultHigh : Option (PanSemResultExact width) × PanSemExactEvalContext width σ)
    (hLow : evalPanSemRecursiveCallContextHOLExact program context = some resultLow)
    (hHigh : evalPanSemRecursiveCallContextHOLExact program (ctxAddClock context extra) =
      some resultHigh) :
    resultLow.2.state.ffi.ioEvents <+: resultHigh.2.state.ffi.ioEvents :=
  (eval_add_clock_mono_aux program context extra resultLow resultHigh hLow hHigh).1

/-- Clock-increase event-trace prefix in terms of the (total) evaluator
outputs, eliminating the always-present assembly marker. -/
theorem evalPanSemRecursiveCallContextHOLExact_add_clock_ioEvents_prefix_getD
    {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) (context : PanSemExactEvalContext width σ) (extra : Nat) :
    ((evalPanSemRecursiveCallContextHOLExact program context).map
        (fun result => result.2.state.ffi.ioEvents)).getD [] <+:
      ((evalPanSemRecursiveCallContextHOLExact program (ctxAddClock context extra)).map
        (fun result => result.2.state.ffi.ioEvents)).getD [] := by
  obtain ⟨resultLow, hLow⟩ :=
    evalPanSemRecursiveCallContextHOLExact_total program context
  obtain ⟨resultHigh, hHigh⟩ :=
    evalPanSemRecursiveCallContextHOLExact_total program (ctxAddClock context extra)
  simp only [hLow, hHigh, Option.map_some, Option.getD_some]
  exact (eval_add_clock_mono_aux program context extra resultLow resultHigh hLow hHigh).1

end Flapjack
