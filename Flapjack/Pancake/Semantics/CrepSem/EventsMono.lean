import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Pancake.Semantics.CrepSem.EvaluateInd

/-!
# FFI event-prefix monotonicity of the exact Crep evaluator

This module proves the `evalCrepSemHOLProg` (and no-decider
`evalCrepSemHOLProgExact`) analogue of HOL
`crepPropsScript.sml:957 evaluate_io_events_mono`:

```
!exps s1 res s2. evaluate (exps,s1) = (res,s2) ==> s1.ffi.io_events ≼ s2.ffi.io_events
```

HOL proves it by `recInduct evaluate_ind` plus `IS_PREFIX_TRANS`: only the
shared-memory (`sh_mem_load`/`sh_mem_store`) and external-call leaves extend
`ffi.ioEvents` (through `call_FFI`), every other clause preserves `ffi`, and the
recursive clauses compose the sub-evaluations' prefixes. The declarations below
mirror that structure. They are Flapjack-internal infrastructure (no `@[hol]`
tag); the tagged public theorem is `Flapjack.crepPropsEvaluateIoEventsMono` in the
`crepPropsScript.sml` counterpart module `CrepProps.lean`.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

/-- Domain stamping preserves the FFI component, so a prefix established for the
    stamped state's `ffi` also holds for the original. -/
theorem crepStampExactDomains_ioEvents_eq {width : Nat} [NeZero width] {σ : Type}
    (base state : CrepSemHOLState width σ) :
    (crepStampExactDomains base state).ffi.ioEvents = state.ffi.ioEvents := rfl

/-- `empty_locals` preserves the FFI component. -/
theorem CrepSemHOLState.emptyLocals_ioEvents_eq {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    (CrepSemHOLState.emptyLocals state).ffi.ioEvents = state.ffi.ioEvents := rfl

/-- `fix_clock` preserves the FFI component of the result state. -/
theorem fixClockCrepSemHOL_ioEvents_eq {width : Nat} [NeZero width] {σ : Type} {β : Type}
    (oldState : CrepSemHOLState width σ) (step : β × CrepSemHOLState width σ) :
    (fixClockCrepSemHOL oldState step).2.ffi.ioEvents = step.2.ffi.ioEvents := rfl

/-- The `While` loop-control case split cannot discard an earlier event prefix:
    the recursive branches use the `While` IH, the `Break 0`/pass-through
    branches keep the `fix_clock` state, and the loop step itself only extends
    the log. Mirrors HOL `evaluate_io_events_mono`'s `While` case. -/
theorem crepWhileStep_ioEvents_prefix {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (condition : CrepExpHOL width) (body : CrepProgHOL width)
    (loopStep : Option (CrepResultHOLExact width) × CrepSemHOLState width σ)
    (hstep : state.ffi.ioEvents <+: loopStep.2.ffi.ioEvents)
    (hrec : (crepStampExactDomains state loopStep.2).ffi.ioEvents <+:
      (evalCrepSemHOLProg (crepStampExactDomains state loopStep.2) memDec shMemDec
        (.while condition body)).2.ffi.ioEvents) :
    state.ffi.ioEvents <+:
      (match _hloopStep : loopStep with
       | (none, loopState) =>
           evalCrepSemHOLProg (crepStampExactDomains state loopState) memDec shMemDec
             (.while condition body)
       | (some (.continue 0), loopState) =>
           evalCrepSemHOLProg (crepStampExactDomains state loopState) memDec shMemDec
             (.while condition body)
       | (some (.break 0), loopState) => (none, loopState)
       | (result, loopState) => (exitLoopCrepResult result, loopState)).2.ffi.ioEvents := by
  have hstep' : state.ffi.ioEvents <+: (crepStampExactDomains state loopStep.2).ffi.ioEvents := by
    simpa using hstep
  split
  · exact hstep'.trans hrec
  · exact hstep'.trans hrec
  · exact hstep'
  · exact hstep'

/-- The `Call` callee-result case split cannot discard an earlier event prefix:
    the exception-handler branch uses the handler IH, every other branch keeps
    the `fix_clock` body state. Mirrors HOL `evaluate_io_events_mono`'s `Call`
    case. -/
theorem crepCallFixed_ioEvents_prefix {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (returnInfo : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fixed : Option (CrepResultHOLExact width) × CrepSemHOLState width σ)
    (hfix : state.ffi.ioEvents <+: fixed.2.ffi.ioEvents)
    (hhandler : ∀ (handlerBody : CrepProgHOL width),
      state.ffi.ioEvents <+:
        (evalCrepSemHOLProg
          (crepStampExactDomains state { fixed.2 with locals := state.locals })
          memDec shMemDec handlerBody).2.ffi.ioEvents) :
    state.ffi.ioEvents <+:
      (match _hcallFixed : fixed with
       | (none, bodyState) => (some CrepResultHOLExact.error, bodyState)
       | (some (CrepResultHOLExact.break _), bodyState) =>
           (some CrepResultHOLExact.error, bodyState)
       | (some (CrepResultHOLExact.continue _), bodyState) =>
           (some CrepResultHOLExact.error, bodyState)
       | (some (CrepResultHOLExact.return retvs), bodyState) =>
           match returnInfo with
           | none => (some (CrepResultHOLExact.return retvs),
               CrepSemHOLState.emptyLocals bodyState)
           | some (rts, _) =>
               if retvs.length ≠ rts.length then
                 (some CrepResultHOLExact.error, bodyState)
               else match rts.mapM state.locals.lookup with
                 | some _ => (none, { bodyState with
                     locals := state.locals.updateListEq (rts.zip retvs) })
                 | none => (some CrepResultHOLExact.error, bodyState)
       | (some (CrepResultHOLExact.exception eid), bodyState) =>
           match returnInfo with
           | none =>
               (some (CrepResultHOLExact.exception eid),
                 CrepSemHOLState.emptyLocals bodyState)
           | some (_, none) =>
               (some (CrepResultHOLExact.exception eid),
                 CrepSemHOLState.emptyLocals bodyState)
           | some (_, some (eid', handlerBody)) =>
               if eid = eid' then
                 evalCrepSemHOLProg
                   (crepStampExactDomains state { bodyState with locals := state.locals })
                   memDec shMemDec handlerBody
               else (some (CrepResultHOLExact.exception eid),
                 CrepSemHOLState.emptyLocals bodyState)
       | (some result, bodyState) =>
           (some result, CrepSemHOLState.emptyLocals bodyState)).2.ffi.ioEvents := by
  split
  · exact hfix
  · exact hfix
  · exact hfix
  · split
    · exact hfix
    · split
      · exact hfix
      · split <;> exact hfix
  · split
    · exact hfix
    · exact hfix
    · split
      · exact hhandler _
      · exact hfix
  · exact hfix

/-- The total exact `crepSem$evaluate` port `evalCrepSemHOLProg` only ever
    extends the FFI event log. Proved by HOL's `evaluate_ind`-shaped
    clock/program-size recursion: only the shared-memory and external-call
    leaves call `call_FFI`, whose returned/`final` forms keep or extend the log,
    and the recursive clauses compose the sub-runs by `IS_PREFIX_TRANS`. This is
    the `evalCrepSemHOLProg` core lemma for HOL
    `crepPropsScript.sml:957 evaluate_io_events_mono`. Untagged infrastructure:
    the tagged public theorem is `crepPropsEvaluateIoEventsMono`. -/
theorem evalCrepSemHOLProg_ioEvents_prefix {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (program : CrepProgHOL width) :
    state.ffi.ioEvents <+:
      (evalCrepSemHOLProg state memDec shMemDec program).2.ffi.ioEvents := by
  have hmain : ∀ (c : Nat) (state : CrepSemHOLState width σ), state.clock ≤ c →
      ∀ (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
        (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
        (program : CrepProgHOL width),
        state.ffi.ioEvents <+:
          (evalCrepSemHOLProg state memDec shMemDec program).2.ffi.ioEvents := by
    intro c
    induction c using Nat.strongRecOn with
    | ind c ihClock =>
      intro state hclk memDec shMemDec program
      have inner : ∀ (n : Nat) (program : CrepProgHOL width), sizeOf program ≤ n →
          ∀ (state : CrepSemHOLState width σ), state.clock ≤ c →
          ∀ (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
            (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a)),
            state.ffi.ioEvents <+:
              (evalCrepSemHOLProg state memDec shMemDec program).2.ffi.ioEvents := by
        intro n
        induction n using Nat.strongRecOn with
        | ind n ihSize =>
          intro program hsize state hclk memDec shMemDec
          cases program with
          | skip =>
              rw [evalCrepSemHOLProg_skip]
              exact List.prefix_refl _
          | dec name value body =>
              have hsub : sizeOf body < n := by
                have h1 : sizeOf body < sizeOf (CrepProgHOL.dec name value body) := by
                  decreasing_trivial
                omega
              rw [evalCrepSemHOLProg_dec_ffi]
              cases hcond : crepExactEvalExp state memDec value with
              | none => exact List.prefix_refl _
              | some v =>
                  have hBody := ihSize (sizeOf body) hsub body (by omega)
                    (CrepSemHOLState.setVar name v state)
                    (by simpa [CrepSemHOLState.setVar] using hclk) memDec shMemDec
                  simpa [CrepSemHOLState.setVar] using hBody
          | assign name src =>
              rw [evalCrepSemHOLProg_assign_ffi]
              exact List.prefix_refl _
          | primitive names operator args =>
              rw [evalCrepSemHOLProg_primitive_ffi]
              exact List.prefix_refl _
          | store dst src =>
              rw [evalCrepSemHOLProg_store_ffi]
              exact List.prefix_refl _
          | store32 dst src =>
              rw [evalCrepSemHOLProg_store32_ffi]
              exact List.prefix_refl _
          | storeByte dst src =>
              rw [evalCrepSemHOLProg_storeByte_ffi]
              exact List.prefix_refl _
          | storeGlob dst src =>
              rw [evalCrepSemHOLProg_storeGlob_ffi]
              exact List.prefix_refl _
          | seq first second =>
              have hsubF : sizeOf first < n := by
                have h1 : sizeOf first < sizeOf (CrepProgHOL.seq first second) := by
                  decreasing_trivial
                omega
              have hsubS : sizeOf second < n := by
                have h1 : sizeOf second < sizeOf (CrepProgHOL.seq first second) := by
                  decreasing_trivial
                omega
              have ihFirst := ihSize (sizeOf first) hsubF first (by omega) state hclk
                memDec shMemDec
              rw [evalCrepSemHOLProg_seq_ffi]
              generalize hfix :
                fixClockCrepSemHOL state (evalCrepSemHOLProg state memDec shMemDec first) =
                  fixed
              cases fixed with
              | mk res stepState =>
                cases res with
                | none =>
                    have hstepFfi :
                        (evalCrepSemHOLProg state memDec shMemDec first).2.ffi =
                          stepState.ffi := by
                      have := congrArg (fun p : Option (CrepResultHOLExact width) ×
                          CrepSemHOLState width σ => p.2.ffi) hfix
                      simpa [fixClockCrepSemHOL] using this
                    have hstate : state.ffi.ioEvents <+: stepState.ffi.ioEvents := by
                      simpa [hstepFfi] using ihFirst
                    have hclk2 : (crepStampExactDomains state stepState).clock ≤ c := by
                      have hb := fixClockCrepSemHOL_IMP_LESS_EQ state
                        (evalCrepSemHOLProg state memDec shMemDec first) none stepState
                        (by simpa using hfix)
                      change stepState.clock ≤ c
                      omega
                    have ihSecond := ihSize (sizeOf second) hsubS second (by omega)
                      (crepStampExactDomains state stepState) hclk2 memDec shMemDec
                    have hstamp := crepStampExactDomains_ioEvents_eq state stepState
                    rw [hstamp] at ihSecond
                    exact hstate.trans ihSecond
                | some res =>
                    have hstepFfi :
                        (evalCrepSemHOLProg state memDec shMemDec first).2.ffi =
                          stepState.ffi := by
                      have := congrArg (fun p : Option (CrepResultHOLExact width) ×
                          CrepSemHOLState width σ => p.2.ffi) hfix
                      simpa [fixClockCrepSemHOL] using this
                    simpa [hstepFfi] using ihFirst
          | ite condition thenBranch elseBranch =>
              have hsubT : sizeOf thenBranch < n := by
                have h1 : sizeOf thenBranch <
                    sizeOf (CrepProgHOL.ite condition thenBranch elseBranch) := by
                  decreasing_trivial
                omega
              have hsubE : sizeOf elseBranch < n := by
                have h1 : sizeOf elseBranch <
                    sizeOf (CrepProgHOL.ite condition thenBranch elseBranch) := by
                  decreasing_trivial
                omega
              have ihThen := ihSize (sizeOf thenBranch) hsubT thenBranch (by omega) state
                hclk memDec shMemDec
              have ihElse := ihSize (sizeOf elseBranch) hsubE elseBranch (by omega) state
                hclk memDec shMemDec
              rw [evalCrepSemHOLProg_ite_ffi]
              cases hcond : crepExactEvalExp state memDec condition with
              | none => exact List.prefix_refl _
              | some value =>
                  cases value with
                  | word w =>
                      dsimp only
                      split
                      · exact ihThen
                      · exact ihElse
          | «while» condition body =>
              rw [evalCrepSemHOLProg_while]
              split
              · rename_i w
                split
                · split
                  · simp [CrepSemHOLState.emptyLocals]
                  · dsimp only
                    have ihBody := ihClock (decClockCrepSemHOL state).clock
                        (by simp only [decClockCrepSemHOL]; omega)
                        (decClockCrepSemHOL state)
                        (by simp only [decClockCrepSemHOL]; omega) memDec shMemDec body
                    refine crepWhileStep_ioEvents_prefix state memDec shMemDec condition body
                      (fixClockCrepSemHOL (decClockCrepSemHOL state)
                        (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec
                          body)) ?_ ?_
                    · simpa [fixClockCrepSemHOL, decClockCrepSemHOL] using ihBody
                    · have hloopClock :
                          (crepStampExactDomains state
                            (fixClockCrepSemHOL (decClockCrepSemHOL state)
                              (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec
                                body)).2).clock < c := by
                        have hb : (fixClockCrepSemHOL (decClockCrepSemHOL state)
                              (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec
                                body)).2.clock ≤ (decClockCrepSemHOL state).clock :=
                          fixClockCrepSemHOL_IMP_LESS_EQ (decClockCrepSemHOL state)
                            (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec
                              body) _ _ rfl
                        have hb2 : (decClockCrepSemHOL state).clock < c := by
                          simp only [decClockCrepSemHOL]; omega
                        change (fixClockCrepSemHOL (decClockCrepSemHOL state)
                          (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec
                            body)).2.clock < c
                        omega
                      exact ihClock
                        (crepStampExactDomains state
                          (fixClockCrepSemHOL (decClockCrepSemHOL state)
                            (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec
                              body)).2).clock hloopClock
                        (crepStampExactDomains state
                          (fixClockCrepSemHOL (decClockCrepSemHOL state)
                            (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec
                              body)).2)
                        (by omega) memDec shMemDec
                        (.while condition body)
                · exact List.prefix_refl _
              · exact List.prefix_refl _
          | «break» label =>
              rw [evalCrepSemHOLProg_break_ffi]
              exact List.prefix_refl _
          | «continue» label =>
              rw [evalCrepSemHOLProg_continue_ffi]
              exact List.prefix_refl _
          | «return» values =>
              rw [evalCrepSemHOLProg_return_ffi]
              exact List.prefix_refl _
          | raise exception =>
              rw [evalCrepSemHOLProg_raise_ffi]
              exact List.prefix_refl _
          | tick =>
              rw [evalCrepSemHOLProg_tick_ffi]
              exact List.prefix_refl _
          | shMem operator name address =>
              rw [evalCrepSemHOLProg_shMem_ffi]
              cases hcond : crepExactEvalExp state memDec address with
              | none => exact List.prefix_refl _
              | some value =>
                  cases value with
                  | word addressValue =>
                      cases hb : crepIsLoadMemOp operator with
                      | true =>
                          cases hlook : state.locals.lookup name with
                          | none => exact List.prefix_refl _
                          | some v =>
                              exact crepShMemLoadHOL_ioEvents_prefix operator name
                                addressValue state shMemDec
                      | false =>
                          cases hlook : state.locals.lookup name with
                          | none => exact List.prefix_refl _
                          | some v =>
                              cases v with
                              | word w =>
                                  exact crepShMemStoreHOL_ioEvents_prefix operator name
                                    addressValue state shMemDec
          | extCall function configuration configurationLength array arrayLength =>
              rw [evalCrepSemHOLProg_extCall_ffi]
              split
              · split
                · cases hc : callFFIHOL state.ffi (.extCall function) _ _
                    with
                  | final event => exact List.prefix_refl _
                  | ret newFfi newBytes =>
                      exact callFFIHOL_return_ioEvents_prefix state.ffi
                        (.extCall function) _ _ newFfi newBytes hc
                · exact List.prefix_refl _
              · exact List.prefix_refl _
          | call calleeInfo function arguments =>
              rw [evalCrepSemHOLProg_call]
              split
              · exact List.prefix_refl _
              · rename_i values _
                split
                · exact List.prefix_refl _
                · rename_i parameters body _
                  split
                  · dsimp only
                    split
                    · rename_i rts snd
                      split
                      · dsimp only
                        split
                        · simp [CrepSemHOLState.emptyLocals]
                        · have ihBody := ihClock
                              (decClockCrepSemHOL
                                { state with locals :=
                                  HolFiniteMapExact.empty.updateList (parameters.zip values) }).clock
                              (by simp only [decClockCrepSemHOL]; omega)
                              (decClockCrepSemHOL
                                { state with locals :=
                                  HolFiniteMapExact.empty.updateList (parameters.zip values) })
                              (by simp only [decClockCrepSemHOL]; omega) memDec shMemDec body
                          have hbodyState : state.ffi.ioEvents <+:
                              (fixClockCrepSemHOL
                                (decClockCrepSemHOL
                                  { state with locals :=
                                    HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                (evalCrepSemHOLProg
                                  (decClockCrepSemHOL
                                    { state with locals :=
                                      HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                  memDec shMemDec body)).2.ffi.ioEvents := by
                            simpa [fixClockCrepSemHOL, decClockCrepSemHOL] using ihBody
                          exact crepCallFixed_ioEvents_prefix state memDec shMemDec
                            (some (rts, snd))
                            (fixClockCrepSemHOL
                              (decClockCrepSemHOL
                                { state with locals :=
                                  HolFiniteMapExact.empty.updateList (parameters.zip values) })
                              (evalCrepSemHOLProg
                                (decClockCrepSemHOL
                                  { state with locals :=
                                    HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                memDec shMemDec body))
                            hbodyState
                            (fun handlerBody => by
                              have hhandlerClock :
                                  (crepStampExactDomains state
                                    { (fixClockCrepSemHOL
                                        (decClockCrepSemHOL
                                          { state with locals :=
                                            HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                        (evalCrepSemHOLProg
                                          (decClockCrepSemHOL
                                            { state with locals :=
                                              HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                          memDec shMemDec body)).2 with
                                      locals := state.locals }).clock < c := by
                                change (fixClockCrepSemHOL
                                    (decClockCrepSemHOL
                                      { state with locals :=
                                        HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                    (evalCrepSemHOLProg
                                      (decClockCrepSemHOL
                                        { state with locals :=
                                          HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                      memDec shMemDec body)).2.clock < c
                                have hb : (fixClockCrepSemHOL
                                      (decClockCrepSemHOL
                                        { state with locals :=
                                          HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                      (evalCrepSemHOLProg
                                        (decClockCrepSemHOL
                                          { state with locals :=
                                            HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                        memDec shMemDec body)).2.clock ≤
                                    (decClockCrepSemHOL
                                      { state with locals :=
                                        HolFiniteMapExact.empty.updateList (parameters.zip values) }).clock :=
                                  fixClockCrepSemHOL_IMP_LESS_EQ
                                    (decClockCrepSemHOL
                                      { state with locals :=
                                        HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                    (evalCrepSemHOLProg
                                      (decClockCrepSemHOL
                                        { state with locals :=
                                          HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                      memDec shMemDec body) _ _ rfl
                                have hb2 : (decClockCrepSemHOL
                                    { state with locals :=
                                      HolFiniteMapExact.empty.updateList (parameters.zip values) }).clock < c := by
                                  simp only [decClockCrepSemHOL]; omega
                                omega
                              have ihHandler := ihClock
                                (crepStampExactDomains state
                                  { (fixClockCrepSemHOL
                                      (decClockCrepSemHOL
                                        { state with locals :=
                                          HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                      (evalCrepSemHOLProg
                                        (decClockCrepSemHOL
                                          { state with locals :=
                                            HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                        memDec shMemDec body)).2 with
                                    locals := state.locals }).clock hhandlerClock
                                (crepStampExactDomains state
                                  { (fixClockCrepSemHOL
                                      (decClockCrepSemHOL
                                        { state with locals :=
                                          HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                      (evalCrepSemHOLProg
                                        (decClockCrepSemHOL
                                          { state with locals :=
                                            HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                        memDec shMemDec body)).2 with
                                    locals := state.locals })
                                (by omega) memDec shMemDec handlerBody
                              exact hbodyState.trans ihHandler)
                      · exact List.prefix_refl _
                    · dsimp only
                      split
                      · simp [CrepSemHOLState.emptyLocals]
                      · have ihBody := ihClock
                            (decClockCrepSemHOL
                              { state with locals :=
                                HolFiniteMapExact.empty.updateList (parameters.zip values) }).clock
                            (by simp only [decClockCrepSemHOL]; omega)
                            (decClockCrepSemHOL
                              { state with locals :=
                                HolFiniteMapExact.empty.updateList (parameters.zip values) })
                            (by simp only [decClockCrepSemHOL]; omega) memDec shMemDec body
                        have hbodyState : state.ffi.ioEvents <+:
                            (fixClockCrepSemHOL
                              (decClockCrepSemHOL
                                { state with locals :=
                                  HolFiniteMapExact.empty.updateList (parameters.zip values) })
                              (evalCrepSemHOLProg
                                (decClockCrepSemHOL
                                  { state with locals :=
                                    HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                memDec shMemDec body)).2.ffi.ioEvents := by
                          simpa [fixClockCrepSemHOL, decClockCrepSemHOL] using ihBody
                        exact crepCallFixed_ioEvents_prefix state memDec shMemDec
                            (none)
                            (fixClockCrepSemHOL
                              (decClockCrepSemHOL
                                { state with locals :=
                                  HolFiniteMapExact.empty.updateList (parameters.zip values) })
                              (evalCrepSemHOLProg
                                (decClockCrepSemHOL
                                  { state with locals :=
                                    HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                memDec shMemDec body))
                            hbodyState
                            (fun handlerBody => by
                              have hhandlerClock :
                                  (crepStampExactDomains state
                                    { (fixClockCrepSemHOL
                                        (decClockCrepSemHOL
                                          { state with locals :=
                                            HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                        (evalCrepSemHOLProg
                                          (decClockCrepSemHOL
                                            { state with locals :=
                                              HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                          memDec shMemDec body)).2 with
                                      locals := state.locals }).clock < c := by
                                change (fixClockCrepSemHOL
                                    (decClockCrepSemHOL
                                      { state with locals :=
                                        HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                    (evalCrepSemHOLProg
                                      (decClockCrepSemHOL
                                        { state with locals :=
                                          HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                      memDec shMemDec body)).2.clock < c
                                have hb : (fixClockCrepSemHOL
                                      (decClockCrepSemHOL
                                        { state with locals :=
                                          HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                      (evalCrepSemHOLProg
                                        (decClockCrepSemHOL
                                          { state with locals :=
                                            HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                        memDec shMemDec body)).2.clock ≤
                                    (decClockCrepSemHOL
                                      { state with locals :=
                                        HolFiniteMapExact.empty.updateList (parameters.zip values) }).clock :=
                                  fixClockCrepSemHOL_IMP_LESS_EQ
                                    (decClockCrepSemHOL
                                      { state with locals :=
                                        HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                    (evalCrepSemHOLProg
                                      (decClockCrepSemHOL
                                        { state with locals :=
                                          HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                      memDec shMemDec body) _ _ rfl
                                have hb2 : (decClockCrepSemHOL
                                    { state with locals :=
                                      HolFiniteMapExact.empty.updateList (parameters.zip values) }).clock < c := by
                                  simp only [decClockCrepSemHOL]; omega
                                omega
                              have ihHandler := ihClock
                                (crepStampExactDomains state
                                  { (fixClockCrepSemHOL
                                      (decClockCrepSemHOL
                                        { state with locals :=
                                          HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                      (evalCrepSemHOLProg
                                        (decClockCrepSemHOL
                                          { state with locals :=
                                            HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                        memDec shMemDec body)).2 with
                                    locals := state.locals }).clock hhandlerClock
                                (crepStampExactDomains state
                                  { (fixClockCrepSemHOL
                                      (decClockCrepSemHOL
                                        { state with locals :=
                                          HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                      (evalCrepSemHOLProg
                                        (decClockCrepSemHOL
                                          { state with locals :=
                                            HolFiniteMapExact.empty.updateList (parameters.zip values) })
                                        memDec shMemDec body)).2 with
                                    locals := state.locals })
                                (by omega) memDec shMemDec handlerBody
                              exact hbodyState.trans ihHandler)
                  · exact List.prefix_refl _
      exact inner (sizeOf program) program (by omega) state hclk memDec shMemDec
  exact hmain state.clock state (by omega) memDec shMemDec program

/-- The no-decider public evaluator `evalCrepSemHOLProgExact` only ever extends
    the FFI event log. Immediate corollary of
    `evalCrepSemHOLProg_ioEvents_prefix` through
    `evalCrepSemHOLProgExact_eq_core`. Untagged infrastructure for
    `crepPropsEvaluateIoEventsMono`. -/
theorem evalCrepSemHOLProgExact_ioEvents_prefix {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (program : CrepProgHOL width) :
    state.ffi.ioEvents <+:
      (evalCrepSemHOLProgExact state program).2.ffi.ioEvents := by
  classical
  rw [evalCrepSemHOLProgExact_eq_core state program
    (fun a => Classical.propDecidable (state.memaddrs a))
    (fun a => Classical.propDecidable (state.shMemaddrs a))]
  exact evalCrepSemHOLProg_ioEvents_prefix state _ _ program

end Flapjack
