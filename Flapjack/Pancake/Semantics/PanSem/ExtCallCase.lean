import Flapjack.Pancake.Semantics.PanSem.EvaluateFinite
import Flapjack.Pancake.Semantics.PanSem.ExtCallExact

/-!
# The HOL `evaluate_def` ExtCall equation

This case lives beside the other constructor ports rather than in the shared
recursive evaluator module. The tagged statement exposes the four expression
checks, two byte-array reads, FFI final/return split, and returned memory/FFI
state update from `panSemScript.sml:711-726`.
-/

namespace Flapjack.Pancake.Semantics.PanSem.ExtCallCase

open Flapjack
open Flapjack.Pancake.PanLang (ExpHOL MlS ProgHOL)

/-- The reference checker requires the finite-map representation witness in
    every module that owns a `fmap_as_finite_support`-qualified theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

theorem ofExact_toExact_any {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (support : state.toExact.FiniteSupport) :
    PanSemStateFiniteExact.ofExact state.toExact support = state := by
  cases state
  rfl

theorem ofExact_emptyLocals_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) :
    PanSemStateFiniteExact.ofExact (Flapjack.emptyLocalsHOLExact state.toExact)
      (PanSemStateExact.finiteSupport_emptyLocals state.toExact_finiteSupport) =
      PanSemStateFiniteExact.emptyLocalsHOLFinite state := by
  cases state
  rfl

/-- HOL `evaluate_def`'s `ExtCall` equation (`panSemScript.sml:711-726`,
    theorem line 780). It retains all four source `eval` checks, both
    `read_bytearray` checks, the `call_FFI` result split, and on `FFI_return`
    writes bytes at the second address while installing the returned FFI state.
    The only representation qualifier is the reviewed finite-support encoding
    of the four HOL finite-map fields. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 780
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem evaluateHOLFiniteState_extCall_source {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    (function : MlS) (configuration configurationLength array arrayLength : ExpHOL width) :
    PanSemStateFiniteExact.evaluateHOLFiniteState state
        (.extCall function configuration configurationLength array arrayLength : ProgHOL width) =
      match
        @PanSemStateFiniteExact.evalHOLFinite width σ _ state
          (fun address => Classical.propDecidable (state.memaddrs address)) configuration,
        @PanSemStateFiniteExact.evalHOLFinite width σ _ state
          (fun address => Classical.propDecidable (state.memaddrs address)) configurationLength,
        @PanSemStateFiniteExact.evalHOLFinite width σ _ state
          (fun address => Classical.propDecidable (state.memaddrs address)) array,
        @PanSemStateFiniteExact.evalHOLFinite width σ _ state
          (fun address => Classical.propDecidable (state.memaddrs address)) arrayLength with
      | some (.val (.word address1)), some (.val (.word length1)),
        some (.val (.word address2)), some (.val (.word length2)) =>
          match
            readBytearrayWordHOL (byteWidth := 8) address1 length1.toNat
              (@panMemLoadByteWord8HOL width _ state.memory state.memaddrs
                (fun address => Classical.propDecidable (state.memaddrs address)) state.be),
            readBytearrayWordHOL (byteWidth := 8) address2 length2.toNat
              (@panMemLoadByteWord8HOL width _ state.memory state.memaddrs
                (fun address => Classical.propDecidable (state.memaddrs address)) state.be) with
          | some bytes1, some bytes2 =>
              match callFFIHOL state.ffi (.extCall function) bytes1 bytes2 with
              | .final event =>
                  (some (.finalFfi event),
                    PanSemStateFiniteExact.emptyLocalsHOLFinite state)
              | .ret newFfi newBytes =>
                  let nextState : PanSemStateExact width σ :=
                    { state.toExact with
                      memory := @panWriteBytearrayWord8HOL width _ address2 newBytes
                        state.memory state.memaddrs
                        (fun address => Classical.propDecidable (state.memaddrs address))
                        state.be
                      ffi := newFfi }
                  (none, PanSemStateFiniteExact.ofExact nextState (by
                    change nextState.FiniteSupport
                    simpa [nextState, PanSemStateExact.FiniteSupport] using
                      state.toExact_finiteSupport))
          | _, _ => (some .error, state)
      | _, _, _, _ => (some .error, state) := by
  classical
  simp [PanSemStateFiniteExact.evaluateHOLFiniteState,
    PanSemStateFiniteExact.evaluateHOLFiniteStateWithDeciders,
    PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext,
    PanSemStateFiniteExact.evalPanSemNonrecursiveHOLFinite,
    evalPanSemNonrecursiveHOLExact, extCallStepHOLExact] <;>
    repeat' split <;> simp_all
  all_goals
    first
    | exact ofExact_emptyLocals_toExact state
    | exact PanSemStateFiniteExact.ofExact_toExact
        (PanSemStateFiniteExact.emptyLocalsHOLFinite state)
    | apply ofExact_toExact_any

end Flapjack.Pancake.Semantics.PanSem.ExtCallCase
