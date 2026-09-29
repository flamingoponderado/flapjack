import Flapjack.Pancake.CrepArith
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect
import Flapjack.Pancake.Proofs.CrepArith.HOLStateMapc
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-!
# `ExtCall` case of HOL `crep_arith$simp_prog_correct`

This module specializes HOL's `simp_prog_correct`
(`crep_arithProofScript.sml:184-212`) to the `ExtCall` program constructor.
HOL's `simp_prog` leaves an `ExtCall` unchanged (the catch-all
`simp_prog p = p`, `crep_arithScript.sml:113`), and its `evaluate` clause
(`crepSemScript.sml:367-379`) reads the configuration/array windows through
`mem_load_byte`/`read_bytearray`, calls `call_FFI`, and either finalises with
`(SOME (FinalFFI outcome), s)` or stores the returned bytes with
`(NONE, s with memory := …, ffi := new_ffi)`.

The case keeps the source evaluation equation, the `result ≠ SOME Error` side
condition, and the target evaluation conclusion over the exact `CrepProgHOL`,
`CrepSemHOLState` and `CrepResultHOLExact` carriers.  The `ExtCall` clause never
inspects the code map, so the proof only needs that the code-only `mapcs`
update commutes with the memory/FFI update performed by the FFI return; no
target-result assumption is taken.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

namespace SimpProgCorrectExtCallSupport

/-- Same-module canonical witness for the named finite-map fields on the
    `CrepSemHOLState` carrier used by this HOL-shaped case theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end SimpProgCorrectExtCallSupport

/-- Flapjack-only commuting law: the proof script's local `mapcs` rendering
    changes only the code map, so it commutes with the exact memory/FFI update
    installed by the FFI return branch of `ExtCall`. -/
theorem crepSimpMapcsHOL_withMemoryFfi {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (memory : BitVec width → HolWordLab width)
    (ffi : HolFfiState σ) :
    crepSimpMapcsHOL { state with memory := memory, ffi := ffi } =
      { crepSimpMapcsHOL state with memory := memory, ffi := ffi } := by
  cases state
  rfl

/-- Flapjack-only commutation of the code-only `mapcs` rendering with the exact
    `ExtCall` clause: the clause reads only the locals, memory, address domain,
    endianness and FFI, all of which `mapcs` preserves. -/
theorem evalCrepSemHOLProgExact_extCall_mapcs {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (function : MlString)
    (configuration configurationLength array arrayLength : Nat) :
    evalCrepSemHOLProgExact (crepSimpMapcsHOL state)
        (.extCall function configuration configurationLength array arrayLength) =
      Prod.map id crepSimpMapcsHOL
        (evalCrepSemHOLProgExact state
          (.extCall function configuration configurationLength array arrayLength)) := by
  rw [evalCrepSemHOLProgExact_extCall_holShape, evalCrepSemHOLProgExact_extCall_holShape]
  have hlocals : (crepSimpMapcsHOL state).locals = state.locals := by cases state; rfl
  have hmemory : (crepSimpMapcsHOL state).memory = state.memory := by cases state; rfl
  have hmemaddrs : (crepSimpMapcsHOL state).memaddrs = state.memaddrs := by cases state; rfl
  have hbe : (crepSimpMapcsHOL state).be = state.be := by cases state; rfl
  have hffi : (crepSimpMapcsHOL state).ffi = state.ffi := by cases state; rfl
  rw [hlocals, hmemory, hmemaddrs, hbe, hffi]
  split <;> (try split) <;> (try split) <;> (try split) <;>
    first
    | (simp only [Prod.map, id_eq]; rw [crepSimpMapcsHOL_withMemoryFfi]; rfl)
    | (simp only [Prod.map, id_eq]; rfl)
    | simp_all

/-- The `ExtCall function configuration configurationLength array arrayLength`
    specialization of HOL `simp_prog_correct` (`crep_arithProofScript.sml:184-212`).
    The `result ≠ SOME Error` premise is retained; the `ExtCall` clause never
    inspects the code map, so the code-only `mapcs` update commutes with the
    memory/FFI update of the FFI return branch. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_prog_correct"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem simpProgCorrectExtCallCase {width : Nat} [NeZero width] {σ : Type} :
    ∀ (state : CrepSemHOLState width σ) (function : MlString)
      (configuration configurationLength array arrayLength : Nat)
      (result : Option (CrepResultHOLExact width))
      (finalState : CrepSemHOLState width σ),
      evalCrepSemHOLProgExact state
          (.extCall function configuration configurationLength array arrayLength : CrepProgHOL width) =
        (result, finalState) →
      result ≠ some .error →
      evalCrepSemHOLProgExact (crepSimpMapcsHOL state)
          (crepSimpProgHOL
            (.extCall function configuration configurationLength array arrayLength : CrepProgHOL width)) =
        (result, crepSimpMapcsHOL finalState) := by
  intro state function configuration configurationLength array arrayLength result finalState heval hresult
  have hsimp : crepSimpProgHOL
      (.extCall function configuration configurationLength array arrayLength : CrepProgHOL width) =
      (.extCall function configuration configurationLength array arrayLength : CrepProgHOL width) := by
    simp only [crepSimpProgHOL]
  rw [hsimp]
  have h := evalCrepSemHOLProgExact_extCall_mapcs state function
    configuration configurationLength array arrayLength
  rw [h, heval]
  simp only [Prod.map, id_eq]

end Flapjack
