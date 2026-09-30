import Flapjack.Ffi
import Flapjack.Basis.Pure.MlString
import Flapjack.HolRef
import Flapjack.Misc.LList

/-!
# Exact HOL `ffi_state` carrier

Lean counterpart of `cakeml/semantics/ffi/ffiScript.sml:15-61`.  That script
defines the observable FFI boundary used by the CakeML semantics:

```
Datatype ffi_outcome = FFI_failed | FFI_diverged
Datatype oracle_result = Oracle_return 'ffi (word8 list) | Oracle_final ffi_outcome
Datatype shmem_op = MappedRead | MappedWrite
Datatype ffiname = ExtCall mlstring | SharedMem shmem_op
Type oracle_function = :'ffi -> word8 list -> word8 list -> 'ffi oracle_result
Type oracle = :ffiname -> 'ffi oracle_function
Datatype io_event = IO_event ffiname (word8 list) ((word8 # word8) list)
Datatype final_event = Final_event ffiname (word8 list) (word8 list) ffi_outcome
Datatype ffi_state = <| oracle; ffi_state; io_events |>
Definition initial_ffi_state oc ffi = <| oracle := oc; ffi_state := ffi; io_events := [] |>
Datatype ffi_result = FFI_return ('ffi ffi_state) (word8 list) | FFI_final final_event
```

The carriers below fix the differences from the executable
`Flapjack.Ffi` module: `word8` is the canonical 256-element `BitVec 8` (not
`UInt8`), the external-call name is the exact `mlstring` carrier (not Lean
`String`), and the `ffi_state` field is named `ffiState` mirroring HOL
`ffi_state` (the executable record calls it `state`).  The declarations are
shape-exact ports, tagged against the HOL script.

The executable `FfiState`/`callFfi` boundary and a checked relation to these
carriers (byte codecs for `UInt8`/`BitVec 8` and `String`/`MlString`, plus the
name/event correspondence) are tracked by the same bead
(`flapjack-pxn.18.5.17.1.2`); this module provides the exact source carrier and
a direct HOL oracle for it.
-/

namespace Flapjack

/-- Exact port of HOL `Datatype: ffi_outcome = FFI_failed | FFI_diverged`
    (`cakeml/semantics/ffi/ffiScript.sml:15-17`). -/
@[hol "cakeml/semantics/ffi/ffiScript.sml" "ffi_outcome"]
inductive HolFfiOutcome where
  | failed
  | diverged
  deriving DecidableEq, Repr

/-- Exact port of HOL `Datatype: oracle_result = Oracle_return 'ffi (word8 list)
    | Oracle_final ffi_outcome` (`cakeml/semantics/ffi/ffiScript.sml:19-21`).
    Constructor arity and field order match: the returned constructor carries
    the new `'ffi` state first and the byte list second. -/
@[hol "cakeml/semantics/ffi/ffiScript.sml" "oracle_result"]
inductive HolOracleResult (σ : Type u) where
  | ret (value : σ) (bytes : List (BitVec 8))
  | final (outcome : HolFfiOutcome)
  deriving Repr

/-- Exact port of HOL `Datatype: shmem_op = MappedRead | MappedWrite`
    (`cakeml/semantics/ffi/ffiScript.sml:23-25`). -/
@[hol "cakeml/semantics/ffi/ffiScript.sml" "shmem_op"]
inductive HolShmemOp where
  | mappedRead
  | mappedWrite
  deriving DecidableEq, Repr

/-- Exact port of HOL `Datatype: ffiname = ExtCall mlstring | SharedMem shmem_op`
    (`cakeml/semantics/ffi/ffiScript.sml:27-29`).  The external-call name is the
    faithful `MlString` carrier. -/
@[hol "cakeml/semantics/ffi/ffiScript.sml" "ffiname"]
inductive HolFfiName where
  | extCall (name : Flapjack.Basis.Pure.MlString.MlString)
  | sharedMem (operator : HolShmemOp)
  deriving DecidableEq, Repr

/-- Exact port of HOL
    `Type oracle_function = :'ffi -> word8 list -> word8 list -> 'ffi oracle_result`
    (`cakeml/semantics/ffi/ffiScript.sml:31`). -/
@[hol "cakeml/semantics/ffi/ffiScript.sml" "oracle_function"]
abbrev HolOracleFunction (σ : Type u) :=
  σ → List (BitVec 8) → List (BitVec 8) → HolOracleResult σ

/-- Exact port of HOL `Type oracle = :ffiname -> 'ffi oracle_function`
    (`cakeml/semantics/ffi/ffiScript.sml:32`). -/
@[hol "cakeml/semantics/ffi/ffiScript.sml" "oracle"]
abbrev HolOracle (σ : Type u) := HolFfiName → HolOracleFunction σ

/-- Exact port of HOL
    `Datatype io_event = IO_event ffiname (word8 list) ((word8 # word8) list)`
    (`cakeml/semantics/ffi/ffiScript.sml:41-42`).  The final field is the
    mutable-array map `(input, output)` as in HOL `ZIP (bytes, bytes')`. -/
@[hol "cakeml/semantics/ffi/ffiScript.sml" "io_event"]
structure HolIoEvent where
  name : HolFfiName
  configuration : List (BitVec 8)
  bytes : List (BitVec 8 × BitVec 8)
  deriving DecidableEq, Repr

/-- Exact port of HOL
    `Datatype final_event = Final_event ffiname (word8 list) (word8 list) ffi_outcome`
    (`cakeml/semantics/ffi/ffiScript.sml:44-46`). -/
@[hol "cakeml/semantics/ffi/ffiScript.sml" "final_event"]
structure HolFinalEvent where
  name : HolFfiName
  configuration : List (BitVec 8)
  bytes : List (BitVec 8)
  outcome : HolFfiOutcome
  deriving Repr

/-- Exact port of HOL
    `Datatype ffi_state = <| oracle; ffi_state; io_events |>`
    (`cakeml/semantics/ffi/ffiScript.sml:48-52`).  Field order matches HOL:
    oracle, host state, event list. -/
@[hol "cakeml/semantics/ffi/ffiScript.sml" "ffi_state"]
structure HolFfiState (σ : Type u) where
  oracle : HolOracle σ
  ffiState : σ
  ioEvents : List HolIoEvent

/-- Exact port of HOL
    `Definition initial_ffi_state oc ffi = <| oracle := oc; ffi_state := ffi; io_events := [] |>`
    (`cakeml/semantics/ffi/ffiScript.sml:55-57`). -/
@[hol "cakeml/semantics/ffi/ffiScript.sml" "initial_ffi_state_def"]
def initialHolFfiState (oracle : HolOracle σ) (state : σ) : HolFfiState σ :=
  { oracle := oracle, ffiState := state, ioEvents := [] }

/-- Exact port of HOL
    `Datatype ffi_result = FFI_return ('ffi ffi_state) (word8 list) | FFI_final final_event`
    (`cakeml/semantics/ffi/ffiScript.sml:59-61`). -/
@[hol "cakeml/semantics/ffi/ffiScript.sml" "ffi_result"]
inductive HolFfiResult (σ : Type u) where
  | ret (state : HolFfiState σ) (bytes : List (BitVec 8))
  | final (event : HolFinalEvent)

/-- Exact port of HOL
    `Definition call_FFI st s conf bytes = if s <> ExtCall «» then ... else FFI_return st bytes`
    (`cakeml/semantics/ffi/ffiScript.sml:65-73`).  The empty external-call name is
    the special identity call; a successful oracle return appends an `io_event`
    with `ZIP (bytes, bytes')`, and a length mismatch or terminal oracle result
    becomes `FFI_final`. -/
@[hol "cakeml/semantics/ffi/ffiScript.sml" "call_FFI_def"]
def callFFIHOL (state : HolFfiState σ) (name : HolFfiName)
    (configuration bytes : List (BitVec 8)) : HolFfiResult σ :=
  if name = .extCall (Flapjack.Basis.Pure.MlString.MlString.implode []) then
    .ret state bytes
  else
    match state.oracle name state.ffiState configuration bytes with
    | .ret nextState nextBytes =>
        if nextBytes.length = bytes.length then
          .ret
            { state with
              ffiState := nextState
              ioEvents := state.ioEvents ++
                [{ name := name, configuration := configuration,
                   bytes := bytes.zip nextBytes }] }
            nextBytes
        else
          .final
            { name := name, configuration := configuration, bytes := bytes,
              outcome := .failed }
    | .final outcome =>
        .final
          { name := name, configuration := configuration, bytes := bytes,
            outcome := outcome }

/-- Flapjack-only helper: the terminal-oracle branch of `callFFIHOL`,
stated as an equation lemma so callers avoid reducing the dependent `match`
on the oracle result directly. -/
theorem callFFIHOL_final {σ : Type u} (state : HolFfiState σ) (name : HolFfiName)
    (configuration bytes : List (BitVec 8)) (outcome : HolFfiOutcome)
    (hne : name ≠ .extCall (Flapjack.Basis.Pure.MlString.MlString.implode []))
    (h : state.oracle name state.ffiState configuration bytes = .final outcome) :
    callFFIHOL state name configuration bytes =
      .final { name := name, configuration := configuration, bytes := bytes,
               outcome := outcome } := by
  unfold callFFIHOL
  rw [if_neg hne, h]

/-- Flapjack-only helper: the returning-oracle branch of `callFFIHOL`. -/
theorem callFFIHOL_ret {σ : Type u} (state : HolFfiState σ) (name : HolFfiName)
    (configuration bytes : List (BitVec 8)) (nextState : σ) (nextBytes : List (BitVec 8))
    (hne : name ≠ .extCall (Flapjack.Basis.Pure.MlString.MlString.implode []))
    (h : state.oracle name state.ffiState configuration bytes = .ret nextState nextBytes) :
    callFFIHOL state name configuration bytes =
      (if nextBytes.length = bytes.length then
        .ret
          { state with
            ffiState := nextState
            ioEvents := state.ioEvents ++
              [{ name := name, configuration := configuration,
                 bytes := bytes.zip nextBytes }] }
          nextBytes
      else
        .final { name := name, configuration := configuration, bytes := bytes,
                 outcome := .failed }) := by
  unfold callFFIHOL
  rw [if_neg hne, h]

/-- Flapjack-only local corollary of the canonical tagged port
`Flapjack.Compiler.Backend.StackRemove.callFFILengthHOL` (HOL `call_FFI_LENGTH`):
a returning (non-final) `callFFIHOL` preserves
    the byte-list length.  On the identity call it returns the input bytes; on
    any other call the returning branch is guarded by `nextBytes.length = bytes.length`.
    Used to feed `stateRelWriteBytearrayHOL` in the `ExtCall` `compile_correct` case.

    HOL analogue: `call_FFI_LENGTH` (`cakeml/compiler/backend/proofs/stack_removeProofScript.sml:67`;
    also `cakeml/semantics/proofs/evaluatePropsScript.sml:13`), whose statement is
    `(call_FFI s i conf xs = FFI_return n ys) ==> (LENGTH ys = LENGTH xs)`.
    This lemma is NOT tagged as that declaration: it is phrased over the Flapjack
    `callFFIHOL` rendering of `call_FFI_def` (already tagged `reviewed_exact` as
    `call_FFI_def` in `cakeml/semantics/ffi/ffiScript.sml`), which carries a
    `HolFfiState σ` and logs `ioEvents` and has an `.extCall`-identity branch that
    the raw HOL `call_FFI` transition does not expose, so the interface differs
    from the stack_removeProofScript statement. -/
theorem callFFIHOL_ret_length {σ : Type u} (state : HolFfiState σ) (name : HolFfiName)
    (configuration bytes nextBytes : List (BitVec 8)) (nextState : HolFfiState σ)
    (h : callFFIHOL state name configuration bytes = .ret nextState nextBytes) :
    nextBytes.length = bytes.length := by
  unfold callFFIHOL at h
  by_cases hid : name = .extCall (Flapjack.Basis.Pure.MlString.MlString.implode [])
  · rw [if_pos hid] at h
    injection h with _ hbytes
    rw [← hbytes]
  · rw [if_neg hid] at h
    cases hor : state.oracle name state.ffiState configuration bytes with
    | ret ns nb =>
        simp only [hor] at h
        by_cases hl : nb.length = bytes.length
        · rw [if_pos hl] at h
          injection h with _ hb
          rw [← hb]; exact hl
        · rw [if_neg hl] at h
          exact absurd h (by simp)
    | final outcome =>
        simp only [hor] at h
        exact absurd h (by simp)

/-- Flapjack-specific call lemma (no standalone HOL declaration): when a
    successful non-identity FFI call leaves the observable event log
    unchanged, it also leaves the complete FFI state unchanged. A successful
    non-identity call appends exactly one event, so the unchanged-log case can
    only be the empty-name identity call. -/
theorem callFFIHOL_ret_ffi_eq_of_ioEvents_eq {σ : Type u}
    (state next : HolFfiState σ) (name : HolFfiName)
    (configuration bytes nextBytes : List (BitVec 8))
    (hcall : callFFIHOL state name configuration bytes = .ret next nextBytes)
    (hevents : next.ioEvents = state.ioEvents) :
    next = state := by
  by_cases hname : name = .extCall (Flapjack.Basis.Pure.MlString.MlString.implode [])
  · subst name
    simp [callFFIHOL] at hcall
    rcases hcall with ⟨hnext, _⟩
    exact hnext.symm
  · unfold callFFIHOL at hcall
    rw [if_neg hname] at hcall
    cases horacle : state.oracle name state.ffiState configuration bytes with
    | final outcome => simp [horacle] at hcall
    | ret hostState returnedBytes =>
        by_cases hlength : returnedBytes.length = bytes.length
        · simp [horacle, hlength] at hcall
          rcases hcall with ⟨hnext, _⟩
          rw [← hnext] at hevents
          have hlengthEvents := congrArg List.length hevents
          simp at hlengthEvents
        · simp [horacle, hlength] at hcall

/-! A single successful exact FFI call cannot discard an earlier observable
    trace.  This is the local transition lemma used when lifting HOL
    `evaluate_io_events_mono` (`cakeml/pancake/semantics/panPropsScript.sml:856`)
    to the exact recursive Pancake evaluator.  It is proved directly from
    `callFFIHOL_def`; no external FFI-extension assumption is needed. -/
theorem callFFIHOL_return_ioEvents_prefix {σ : Type u} (state : HolFfiState σ)
    (name : HolFfiName) (configuration bytes : List (BitVec 8))
    (nextState : HolFfiState σ) (nextBytes : List (BitVec 8))
    (hresult : callFFIHOL state name configuration bytes =
      .ret nextState nextBytes) :
    state.ioEvents <+: nextState.ioEvents := by
  by_cases hname : name = .extCall (Flapjack.Basis.Pure.MlString.MlString.implode [])
  · subst hname
    simp [callFFIHOL] at hresult
    simp_all
  · rw [callFFIHOL] at hresult
    simp only [hname, ↓reduceIte] at hresult
    split at hresult
    · split at hresult
      · cases hresult
        exact List.prefix_append _ _
      · cases hresult
    · cases hresult

/-! The same monotonicity statement in the result's sum form.  The `final`
    branch keeps the current FFI state, while a successful return uses the
    append performed by `callFFIHOL_return_ioEvents_prefix`.  This form is used
    at the exact evaluator's shared-memory and external-call leaves, where the
    result constructor is exposed directly. -/
theorem callFFIHOL_result_ioEvents_prefix {σ : Type u} (state : HolFfiState σ)
    (name : HolFfiName) (configuration bytes : List (BitVec 8))
    (result : HolFfiResult σ)
    (hresult : callFFIHOL state name configuration bytes = result) :
    state.ioEvents <+:
      match result with
      | .ret nextFfi _ => nextFfi.ioEvents
      | .final _ => state.ioEvents := by
  cases result with
  | ret nextFfi nextBytes =>
      exact callFFIHOL_return_ioEvents_prefix state name configuration bytes
        nextFfi nextBytes hresult
  | final event =>
      exact List.prefix_refl _

/-- Exact port of HOL
    `Datatype outcome = Success | Resource_limit_hit | FFI_outcome final_event`
    (`cakeml/semantics/ffi/ffiScript.sml:82-84`). -/
@[hol "cakeml/semantics/ffi/ffiScript.sml" "outcome"]
inductive HolOutcome where
  | success
  | resourceLimitHit
  | ffiOutcome (event : HolFinalEvent)

/-- Exact port of HOL
    `Datatype behaviour = Diverge (io_event llist) | Terminate outcome (io_event list) | Fail`
    (`cakeml/semantics/ffi/ffiScript.sml:89-101`), with HOL's `llist` as the
    rendering `HolLList` of HOL's own `llist` type definition. -/
@[hol "cakeml/semantics/ffi/ffiScript.sml" "behaviour"]
inductive HolBehaviour where
  | diverge (events : HolLList HolIoEvent)
  | terminate (outcome : HolOutcome) (events : List HolIoEvent)
  | fail

end Flapjack
