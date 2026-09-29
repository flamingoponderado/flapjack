import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Pancake.Proofs.CrepArith
import Flapjack.Pancake.Proofs.CrepArith.MulConst

/-!
# Crep arithmetic proof-script state updates

The `mapc` overload and its `FLOOKUP_mapc` equation are local to
`crep_arithProofScript.sml:109`. They live under the `CrepArith` counterpart,
while the carrier itself remains in `Semantics.CrepSem.HOLState`.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString


/-! The canonical finite-map carrier is owned by the Crep semantics module.
This same-module re-export makes its existing kernel-checked roundtrip
available to finite-support qualifiers in the CrepArith counterpart, without
declaring another state carrier. -/
namespace CrepArithSimpExpCorrectWitnesses

theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width]
    {ffiState : Type} :
    (∀ (state : CrepSemBroadState width ffiState) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width ffiState,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end CrepArithSimpExpCorrectWitnesses

/-- Flapjack-only record extensionality for the evaluator-state carrier. -/
private theorem crepHolState_eq_of_fields {α σ : Type}
    {left right : CrepHolState α σ}
    (hLocals : left.locals = right.locals)
    (hGlobals : left.globals = right.globals)
    (hCode : left.code = right.code)
    (hMemory : left.memory = right.memory)
    (hMemaddrs : left.memaddrs = right.memaddrs)
    (hShMemaddrs : left.shMemaddrs = right.shMemaddrs)
    (hClock : left.clock = right.clock)
    (hBigEndian : left.bigEndian = right.bigEndian)
    (hFfi : left.ffi = right.ffi)
    (hBaseAddress : left.baseAddress = right.baseAddress)
    (hTopAddress : left.topAddress = right.topAddress) :
    left = right := by
  cases left
  cases right
  simp_all

/-- HOL's local `mapc f` state update, using `FMAP_MAP2` on the code map. -/
def CrepSemHOLState.mapc {width : Nat} [NeZero width] {σ : Type}
    (f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) : CrepSemHOLState width σ :=
  { state with code := state.code.map2 f }

@[simp] theorem CrepSemHOLState.FLOOKUP_mapc {width : Nat} [NeZero width]
    {σ : Type}
    (f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (name : MlString) :
    (state.mapc f).code.lookup name =
      (state.code.lookup name).map (fun entry => f (name, entry)) := rfl

@[simp] theorem CrepSemHOLState.toExpressionEvaluatorState_mapc
    {width : Nat} [NeZero width] {σ : Type}
    (f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) :
    (state.mapc f).toExpressionEvaluatorState =
      state.toExpressionEvaluatorState := by
  rfl

@[simp] theorem CrepSemHOLState.toBitVecEvaluatorState_mapc
    {width : Nat} [NeZero width] {σ : Type}
    (f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) :
    (state.mapc f).toBitVecEvaluatorState = state.toBitVecEvaluatorState := rfl

/-- HOL's proof-script-local `mapc` update on an arbitrary-index finite state.
This only uses the finite-map `FMAP_MAP2` encoding; it makes no claim about
the code-entry representation. -/
def CrepSemHOLFiniteState.mapc {ι β σ : Type}
    (f : MlString × β → β) (state : CrepSemHOLFiniteState ι β σ) :
    CrepSemHOLFiniteState ι β σ :=
  { state with code := state.code.map2 f }

@[simp] theorem CrepSemHOLFiniteState.toSourceEvaluatorState_mapc
    {ι β σ : Type} (f : MlString × β → β)
    (state : CrepSemHOLFiniteState ι β σ) :
    (state.mapc f).toSourceEvaluatorState = state.toSourceEvaluatorState := rfl

/-- Changing only the HOL code map cannot alter expression evaluation after
projection into the source evaluator. This is Flapjack support for the
`simp_exp_correct1` dependency; the evaluator correspondence to native HOL
remains unproved. -/
theorem evalCrepHolFiniteWordSourceExp_mapc_projection
    {width : Nat} [NeZero width] {σ : Type}
    (f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ)
    (expression : CrepExp (Fin width → Bool)) :
    evalCrepHolFiniteWordSourceExp (instFinHolFiniteDimension (width := width))
        (state.mapc f).toExpressionEvaluatorState expression =
      evalCrepHolFiniteWordSourceExp (instFinHolFiniteDimension (width := width))
        state.toExpressionEvaluatorState expression := by
  rw [CrepSemHOLState.toExpressionEvaluatorState_mapc]

/-- The `memory` field in the all-width expression projection agrees with the
direct BitVec projection after the canonical finite-index conversion. This
representation equation is Flapjack support; it does not identify HOL's
arbitrary `finite_index` type with `Fin width`. -/
theorem CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_memory
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    ((state.toExpressionEvaluatorState).toHolFiniteBitVecState
      (instFinHolFiniteDimension (width := width))).memory =
    state.toBitVecEvaluatorState.memory := by
  funext address
  have hAddress : holWordBitsToBitVec
      (bitVecToHolWord (instFinHolFiniteDimension (width := width)) address) =
      address := by
    change holWordBitsToBitVec
      (holWordToFinBits (instFinHolFiniteDimension (width := width))
        (finBitsToHolWord (instFinHolFiniteDimension (width := width))
          (bitVecToHolWordBits address))) = address
    rw [holWordToFinBits_finBitsToHolWord]
    exact holWordBitsToBitVec_bitVecToHolWordBits address
  dsimp only [CrepSemHOLState.toExpressionEvaluatorState,
    CrepHolState.toHolFiniteBitVecState]
  rw [hAddress]
  cases hCell : state.memory address with
  | word value =>
      simp [CrepSemHOLState.toBitVecEvaluatorState,
        mapCrepHolWordLab, holWordLabToBits_word,
        instFinHolFiniteDimension, hCell]
      change holWordToBitVec
        (instFinHolFiniteDimension (width := width))
        (bitVecToHolWordBits value) = value
      change holWordBitsToBitVec (bitVecToHolWordBits value) = value
      exact holWordBitsToBitVec_bitVecToHolWordBits value

/-- The address-domain field in the expression projection agrees with the
direct BitVec projection after the canonical finite-index conversion. -/
theorem CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_memaddrs
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    ((state.toExpressionEvaluatorState).toHolFiniteBitVecState
      (instFinHolFiniteDimension (width := width))).memaddrs =
    state.toBitVecEvaluatorState.memaddrs := by
  funext address
  have hAddress : holWordBitsToBitVec
      (bitVecToHolWord (instFinHolFiniteDimension (width := width)) address) =
      address := by
    change holWordBitsToBitVec
      (holWordToFinBits (instFinHolFiniteDimension (width := width))
        (finBitsToHolWord (instFinHolFiniteDimension (width := width))
          (bitVecToHolWordBits address))) = address
    rw [holWordToFinBits_finBitsToHolWord]
    exact holWordBitsToBitVec_bitVecToHolWordBits address
  dsimp only [CrepSemHOLState.toExpressionEvaluatorState,
    CrepHolState.toHolFiniteBitVecState]
  rw [hAddress]
  rfl

/-- Finite-map locals survive the expression projection and canonical
finite-index transport unchanged in the direct BitVec view. -/
theorem CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_locals
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    ((state.toExpressionEvaluatorState).toHolFiniteBitVecState
      (instFinHolFiniteDimension (width := width))).locals =
    state.toBitVecEvaluatorState.locals := by
  funext name
  cases hLocal : state.locals.lookup name with
  | none =>
      simp [CrepSemHOLState.toExpressionEvaluatorState,
        CrepSemHOLState.toBitVecEvaluatorState,
        CrepHolState.toHolFiniteBitVecState, hLocal]
  | some cell =>
      cases cell with
      | word value =>
          dsimp only [CrepSemHOLState.toExpressionEvaluatorState,
            CrepSemHOLState.toBitVecEvaluatorState,
            CrepHolState.toHolFiniteBitVecState]
          rw [hLocal]
          simp only [Option.map_some, holWordLabToBits_word, mapCrepHolWordLab,
            HolWordLab.toPanWordLab]
          apply congrArg some
          change PanWordLab.word
            (holWordToBitVec (instFinHolFiniteDimension (width := width))
              (bitVecToHolWordBits value)) = PanWordLab.word value
          congr 1
          change holWordToBitVec
            (instFinHolFiniteDimension (width := width))
            (bitVecToHolWordBits value) = value
          change holWordBitsToBitVec (bitVecToHolWordBits value) = value
          exact holWordBitsToBitVec_bitVecToHolWordBits value

/-- Finite-map globals survive the expression projection and canonical
finite-index transport unchanged in the direct BitVec view. -/
theorem CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_globals
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    ((state.toExpressionEvaluatorState).toHolFiniteBitVecState
      (instFinHolFiniteDimension (width := width))).globals =
    state.toBitVecEvaluatorState.globals := by
  funext name
  cases hGlobal : state.globals.lookup name with
  | none =>
      simp [CrepSemHOLState.toExpressionEvaluatorState,
        CrepSemHOLState.toBitVecEvaluatorState,
        CrepHolState.toHolFiniteBitVecState, hGlobal]
  | some cell =>
      cases cell with
      | word value =>
          dsimp only [CrepSemHOLState.toExpressionEvaluatorState,
            CrepSemHOLState.toBitVecEvaluatorState,
            CrepHolState.toHolFiniteBitVecState]
          rw [hGlobal]
          simp only [Option.map_some, holWordLabToBits_word, mapCrepHolWordLab,
            HolWordLab.toPanWordLab]
          apply congrArg some
          change PanWordLab.word
            (holWordToBitVec (instFinHolFiniteDimension (width := width))
              (bitVecToHolWordBits value)) = PanWordLab.word value
          congr 1
          change holWordToBitVec
            (instFinHolFiniteDimension (width := width))
            (bitVecToHolWordBits value) = value
          change holWordBitsToBitVec (bitVecToHolWordBits value) = value
          exact holWordBitsToBitVec_bitVecToHolWordBits value

/-- The shared-memory domain field also survives the expression projection
and canonical finite-index transport. -/
theorem CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_shMemaddrs
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    ((state.toExpressionEvaluatorState).toHolFiniteBitVecState
      (instFinHolFiniteDimension (width := width))).shMemaddrs =
    state.toBitVecEvaluatorState.shMemaddrs := by
  funext address
  have hAddress : holWordBitsToBitVec
      (bitVecToHolWord (instFinHolFiniteDimension (width := width)) address) =
      address := by
    change holWordBitsToBitVec
      (holWordToFinBits (instFinHolFiniteDimension (width := width))
        (finBitsToHolWord (instFinHolFiniteDimension (width := width))
          (bitVecToHolWordBits address))) = address
    rw [holWordToFinBits_finBitsToHolWord]
    exact holWordBitsToBitVec_bitVecToHolWordBits address
  dsimp only [CrepSemHOLState.toExpressionEvaluatorState,
    CrepHolState.toHolFiniteBitVecState]
  rw [hAddress]
  rfl

/-- The base-address word in the canonical finite-index conversion agrees
with the direct BitVec view. -/
theorem CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_baseAddress
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    ((state.toExpressionEvaluatorState).toHolFiniteBitVecState
      (instFinHolFiniteDimension (width := width))).baseAddress =
    state.toBitVecEvaluatorState.baseAddress := by
  dsimp only [CrepSemHOLState.toExpressionEvaluatorState,
    CrepSemHOLState.toBitVecEvaluatorState,
    CrepHolState.toHolFiniteBitVecState]
  change holWordToBitVec (instFinHolFiniteDimension (width := width))
    (bitVecToHolWordBits state.baseAddr) = state.baseAddr
  change holWordBitsToBitVec (bitVecToHolWordBits state.baseAddr) = state.baseAddr
  exact holWordBitsToBitVec_bitVecToHolWordBits state.baseAddr

/-- The top-address word in the canonical finite-index conversion agrees
with the direct BitVec view. -/
theorem CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_topAddress
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    ((state.toExpressionEvaluatorState).toHolFiniteBitVecState
      (instFinHolFiniteDimension (width := width))).topAddress =
    state.toBitVecEvaluatorState.topAddress := by
  dsimp only [CrepSemHOLState.toExpressionEvaluatorState,
    CrepSemHOLState.toBitVecEvaluatorState,
    CrepHolState.toHolFiniteBitVecState]
  change holWordToBitVec (instFinHolFiniteDimension (width := width))
    (bitVecToHolWordBits state.topAddr) = state.topAddr
  change holWordBitsToBitVec (bitVecToHolWordBits state.topAddr) = state.topAddr
  exact holWordBitsToBitVec_bitVecToHolWordBits state.topAddr

/-- The expression projection followed by the canonical finite-index
transport equals the direct BitVec projection of the same exact state. This
is representation support for all-width evaluator proofs; arbitrary HOL
`finite_index` isomorphism remains a separate requirement. -/
theorem CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    (state.toExpressionEvaluatorState).toHolFiniteBitVecState
      (instFinHolFiniteDimension (width := width)) =
    state.toBitVecEvaluatorState := by
  apply crepHolState_eq_of_fields
  · exact CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_locals state
  · exact CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_globals state
  · rfl
  · exact CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_memory state
  · exact CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_memaddrs state
  · exact CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_shMemaddrs state
  · rfl
  · rfl
  · rfl
  · exact CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_baseAddress state
  · exact CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_topAddress state

/-- The canonical `Fin width` finite-word runtime adapter is definitionally
the existing HOL-word-bits runtime adapter on this exact state. -/
theorem CrepSemHOLState.toHolFiniteWordRuntime_instFin_eq_toHolWordBitsRuntime
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepHolState (Fin width → Bool) σ) :
    state.toHolFiniteWordRuntime (instFinHolFiniteDimension (width := width)) =
    state.toHolWordBitsRuntime := by
  rfl

/-- Full all-width evaluator transport from the exact-state expression
projection to production `evalCrepRuntimeExp`, related to the direct BitVec
HOL-state evaluator. This still uses canonical `Fin width`; it does not claim
the arbitrary HOL `finite_index` instance has been reindexed. -/
theorem evalCrepRuntimeExp_exactCrepSemHOLState_projection
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (expression : CrepExp (Fin width → Bool)) :
    evalCrepRuntimeExp
      (state.toExpressionEvaluatorState.toHolWordBitsRuntime) expression =
    (evalCrepHolExp state.toBitVecEvaluatorState
      (mapCrepExpWord
        (holWordToBitVec (instFinHolFiniteDimension (width := width)))
        expression)).map
      (bitVecToHolWord (instFinHolFiniteDimension (width := width))) := by
  rw [← CrepSemHOLState.toHolFiniteWordRuntime_instFin_eq_toHolWordBitsRuntime]
  calc
    _ = evalCrepHolFiniteDimensionExp
          (instFinHolFiniteDimension (width := width))
          state.toExpressionEvaluatorState expression :=
      evalCrepRuntimeExp_finiteDimension_eq
        (dimension := instFinHolFiniteDimension (width := width))
        (state := state.toExpressionEvaluatorState)
        (expression := expression)
    _ = _ := by
      simp [evalCrepHolFiniteDimensionExp,
        CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState]

/-- The all-width finite-word source `Load32` clause over the exact HOL-shaped
state reduces to the tagged HOL `mem_load_32_def` port on its direct BitVec
projection. This isolates the memory cell, domain, and endian fields from the
recursive `eval_def` proof. It remains untagged: the enclosing evaluator still
uses Flapjack's explicit finite-index projection. -/
theorem evalCrepSemHOLStateSource_load32_eq_memLoad32HOL
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (addressExpression : CrepExp (Fin width → Bool))
    (address : Fin width → Bool)
    (hAddress : evalCrepHolFiniteWordSourceExp
      (instFinHolFiniteDimension (width := width))
      state.toExpressionEvaluatorState addressExpression = some address) :
    (evalCrepHolFiniteWordSourceExp
      (instFinHolFiniteDimension (width := width))
      state.toExpressionEvaluatorState (.load32 addressExpression)).map
        (holWordToBitVec (instFinHolFiniteDimension (width := width))) =
    (panMemLoad32HOL
        (fun bitAddress =>
          (state.toBitVecEvaluatorState.memory bitAddress).toHolWordLab)
        (fun bitAddress => state.toBitVecEvaluatorState.memaddrs bitAddress = true)
        state.toBitVecEvaluatorState.bigEndian
        (holWordToBitVec (instFinHolFiniteDimension (width := width)) address)).map
          (fun value => BitVec.ofNat width value.toNat) := by
  classical
  rw [evalCrepHolFiniteWordSourceExp_load32_eq_panMemLoad32HOL
    (dimension := instFinHolFiniteDimension (width := width))
    (state := state.toExpressionEvaluatorState)
    (addressExpression := addressExpression) (address := address) hAddress]
  rw [CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_memory,
    CrepSemHOLState.toExpressionEvaluatorState_toHolFiniteBitVecState_memaddrs]
  rfl

/-- All-positive-width `simp_exp_correct1` support over the HOL-shaped Crep
state carrier and the proof-script-local `mapc` update. The statement keeps
the unused word_lab result binder, a successful full word_lab evaluation
premise, the exact code-map update, the `n2w` simplifier image, and the full
optional word_lab equality. It remains untagged because evaluation is through
the explicit finite-width source projection after translating exact
`CrepExpHOL` syntax to the evaluator carrier, rather than native HOL
`crepSem$eval`; this theorem does not establish the finite-index instance or
recursive evaluator correspondence. -/
theorem crepSimpExpCorrect1CrepSemHOLStateSource
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ)
    (expression : CrepExpHOL width)
    (_result : HolWordLab width)
    (h : evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := width))
      state.toExpressionEvaluatorState (crepExpHOLToSourceBits expression) ≠ none) :
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := width))
      (state.mapc update).toExpressionEvaluatorState
      (crepSimpExp
        (fun n => bitVecToHolWord
          (instFinHolFiniteDimension (width := width))
          (BitVec.ofNat
            (HolFiniteDimension.width (Fin width)) n))
        (crepExpHOLToSourceBits expression)) =
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := width))
      state.toExpressionEvaluatorState (crepExpHOLToSourceBits expression) := by
  rw [CrepSemHOLState.toExpressionEvaluatorState_mapc]
  letI : HolFiniteDimension (Fin width) :=
    instFinHolFiniteDimension (width := width)
  have hCodeId :
      crepArithHolFiniteDimensionMapCode
        (fun pair : FunName × (List Nat × CrepProg (Fin width → Bool)) => pair.2)
        state.toExpressionEvaluatorState = state.toExpressionEvaluatorState := by
    cases state.toExpressionEvaluatorState
    simp [crepArithHolFiniteDimensionMapCode]
  have hSource := crepSimpExpCorrect1HolFiniteWordSourceWordLab
    (dimension := instFinHolFiniteDimension (width := width))
    (f := fun pair : FunName × (List Nat × CrepProg (Fin width → Bool)) => pair.2)
    state.toExpressionEvaluatorState (crepExpHOLToSourceBits expression)
    (PanWordLab.word (fun _ => false)) h
  rw [hCodeId] at hSource
  exact hSource

/-- All-width `simp_exp_correct1` support over a finite-map state with an
arbitrary finite-index word carrier. The input retains locals, globals, code,
memory, memory domains, clock/endian fields, FFI, and base/top words; its code
update is the actual `FMAP_MAP2`-shaped operation. The unused result binder,
successful full `word_lab` premise, `n2w`-shaped simplifier image, and optional
`word_lab` equality follow HOL's statement shape.

This remains untagged because evaluation is still the explicit-dimension
source projection: the generic code-entry representation and FFI projection
are not identified with HOL's program and FFI carriers, and the recursive
operation clauses have not been proved as a relation to native HOL
`crepSem$eval`. This theorem narrows the state/finite-index gap but does not
close the native evaluator correspondence. -/
theorem crepSimpExpCorrect1CrepSemHOLFiniteStateSource
    {ι β σ : Type} [dimension : HolFiniteDimension ι]
    (update : MlString × β → β)
    (state : CrepSemHOLFiniteState ι β σ)
    (expression : CrepExp (ι → Bool))
    (_result : PanWordLab (ι → Bool))
    (h : evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState expression ≠ none) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      (state.mapc update).toSourceEvaluatorState
      (crepSimpExp
        (fun n => bitVecToHolWord dimension
          (BitVec.ofNat dimension.width n)) expression) =
    evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState expression := by
  rw [CrepSemHOLFiniteState.toSourceEvaluatorState_mapc]
  let projected := state.toSourceEvaluatorState
  let codeId := fun pair : FunName × (List Nat × CrepProg (ι → Bool)) => pair.2
  have hCodeId : crepArithHolFiniteDimensionMapCode codeId projected = projected := by
    cases projected
    simp [crepArithHolFiniteDimensionMapCode, codeId]
  have hPres := crepSimpExpCorrect1HolFiniteWordSourceWordLab
    (dimension := dimension) (f := codeId) projected expression
    (PanWordLab.word (fun _ => false)) h
  rw [hCodeId] at hPres
  exact hPres

/-- Arbitrary-index finite-state `Load` clause for the source evaluator,
matching the `Load` branch of HOL `crepSem$eval_def`
(`crepSemScript.sml:93-98`) and its `mem_load_def` dependency. It retains the
recursive address evaluation, exact total-memory field, address-domain test,
and complete `Option word_lab` result. It stays untagged because evaluation is
still transported through the explicit `HolFiniteDimension` source adapter;
the complete native HOL evaluator/state relation remains open. -/
theorem evalCrepHolFiniteStateSource_load
    {ι β σ : Type} [dimension : HolFiniteDimension ι]
    (state : CrepSemHOLFiniteState ι β σ)
    (addressExpression : CrepExp (ι → Bool)) (address : ι → Bool)
    (hAddress : evalCrepHolFiniteWordSourceExp dimension
      state.toSourceEvaluatorState addressExpression = some address) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState (.load addressExpression) =
    if state.toSourceEvaluatorState.memaddrs address then
      some (state.memory address) else none := by
  let projected := state.toSourceEvaluatorState
  change (evalCrepHolFiniteWordSourceExp dimension projected
      (.load addressExpression)).map PanWordLab.word =
    if projected.memaddrs address then some (state.memory address) else none
  rw [evalCrepHolFiniteWordSourceExp, hAddress]
  simp [panTheWord, projected,
    CrepSemHOLFiniteState.toSourceEvaluatorState]
  cases hMemory : state.memory address with
  | word value =>
      by_cases hDomain : decide (state.memaddrs address) = true <;>
        simp [hDomain]

/-- Arbitrary-index finite-state `Const` case from HOL
`crepSem$eval_def` (`crepSemScript.sml:91`). The entire word_lab wrapper is
preserved. This remains untagged with the enclosing evaluator because its
word type is interpreted through the explicit finite-dimension adapter. -/
theorem evalCrepHolFiniteStateSource_const
    {ι β σ : Type} [dimension : HolFiniteDimension ι]
    (state : CrepSemHOLFiniteState ι β σ) (value : ι → Bool) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState (.const value) =
    some (.word value) := by
  simp [evalCrepHolFiniteWordSourceExpWordLab,
    evalCrepHolFiniteWordSourceExp]

/-- Arbitrary-index finite-state `Var` case from HOL
`crepSem$eval_def` (`crepSemScript.sml:92`). It returns the exact finite-map
lookup, including lookup failure, with no success premise. It remains untagged
because the enclosing evaluator still uses an explicit finite-dimension
projection. -/
theorem evalCrepHolFiniteStateSource_var
    {ι β σ : Type} [dimension : HolFiniteDimension ι]
    (state : CrepSemHOLFiniteState ι β σ) (name : Nat) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState (.var name) =
    state.locals.lookup name := by
  simp [evalCrepHolFiniteWordSourceExpWordLab,
    evalCrepHolFiniteWordSourceExp,
    CrepSemHOLFiniteState.toSourceEvaluatorState,
    panTheWord, Function.comp_def]

/-- Arbitrary-index finite-state `LoadGlob` case from HOL
`crepSem$eval_def` (`crepSemScript.sml:111`). It returns the exact finite-map
global lookup, including a miss. This stays untagged because the enclosing
evaluator/state still use the explicit finite-dimension projection. -/
theorem evalCrepHolFiniteStateSource_loadGlob
    {ι β σ : Type} [dimension : HolFiniteDimension ι]
    (state : CrepSemHOLFiniteState ι β σ) (address : BitVec 5) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState (.loadGlob address) =
    state.globals.lookup address := by
  simp [evalCrepHolFiniteWordSourceExpWordLab,
    evalCrepHolFiniteWordSourceExp,
    CrepSemHOLFiniteState.toSourceEvaluatorState,
    panTheWord, Function.comp_def]

/-- Arbitrary-index finite-state `BaseAddr` case of HOL `eval_def`. The full
`word_lab` value comes directly from the corresponding state field. This
case remains untagged as part of the source evaluator because the explicit
finite-index projection is not yet identified with native HOL `eval`. -/
theorem evalCrepHolFiniteStateSource_baseAddr
    {ι β σ : Type} [dimension : HolFiniteDimension ι]
    (state : CrepSemHOLFiniteState ι β σ) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState .baseAddr =
    some (.word state.baseAddr) := by
  simp [evalCrepHolFiniteWordSourceExpWordLab,
    evalCrepHolFiniteWordSourceExp,
    CrepSemHOLFiniteState.toSourceEvaluatorState]

/-- Arbitrary-index finite-state `TopAddr` case of HOL `eval_def`, with the
complete `word_lab` wrapper. The enclosing evaluator is still the explicit
finite-dimension source projection, so the case does not carry a HOL tag. -/
theorem evalCrepHolFiniteStateSource_topAddr
    {ι β σ : Type} [dimension : HolFiniteDimension ι]
    (state : CrepSemHOLFiniteState ι β σ) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState .topAddr =
    some (.word state.topAddr) := by
  simp [evalCrepHolFiniteWordSourceExpWordLab,
    evalCrepHolFiniteWordSourceExp,
    CrepSemHOLFiniteState.toSourceEvaluatorState]

/-- Arbitrary-index finite-state `Load32` case of HOL `eval_def`, expressed
through the tagged `mem_load_32_def` port after transporting the exact memory
cells to the canonical `BitVec` view. The recursive address hypothesis is the
case induction hypothesis; memory and domains are read from the finite-state
carrier. This remains untagged because the outer source evaluator and
finite-index state relation are not yet native HOL `eval`. -/
theorem evalCrepHolFiniteStateSource_load32
    {ι β σ : Type} [dimension : HolFiniteDimension ι]
    (state : CrepSemHOLFiniteState ι β σ)
    (addressExpression : CrepExp (ι → Bool)) (address : ι → Bool)
    (hAddress : evalCrepHolFiniteWordSourceExp dimension
      state.toSourceEvaluatorState addressExpression = some address) :
    (evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState (.load32 addressExpression)).map
        (mapCrepHolWordLab (holWordToBitVec dimension)) =
    (panMemLoad32HOL
      (fun bitAddress =>
        ((state.toSourceEvaluatorState.toHolFiniteBitVecState dimension).memory
          bitAddress).toHolWordLab)
      (fun bitAddress =>
        (state.toSourceEvaluatorState.toHolFiniteBitVecState dimension).memaddrs
          bitAddress = true)
      state.be (holWordToBitVec dimension address)).map
        (fun value => PanWordLab.word
          (BitVec.ofNat dimension.width value.toNat)) := by
  exact evalCrepHolFiniteWordSourceExpWordLab_load32_eq_panMemLoad32HOL
    dimension state.toSourceEvaluatorState addressExpression address hAddress

/-- Arbitrary-index finite-state `LoadByte` case of HOL `eval_def`, with its
recursive address hypothesis and the complete `word_lab` result transported
to the tagged `mem_load_byte_def` port. The explicit finite-index source
evaluator relation remains open, so this case is not tagged as `eval_def`. -/
theorem evalCrepHolFiniteStateSource_loadByte
    {ι β σ : Type} [dimension : HolFiniteDimension ι]
    (state : CrepSemHOLFiniteState ι β σ)
    (addressExpression : CrepExp (ι → Bool)) (address : ι → Bool)
    (hAddress : evalCrepHolFiniteWordSourceExp dimension
      state.toSourceEvaluatorState addressExpression = some address) :
    (evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState (.loadByte addressExpression)).map
        (mapCrepHolWordLab (holWordToBitVec dimension)) =
    (panMemLoadByteHOL
      (fun bitAddress =>
        ((state.toSourceEvaluatorState.toHolFiniteBitVecState dimension).memory
          bitAddress).toHolWordLab)
      (fun bitAddress =>
        (state.toSourceEvaluatorState.toHolFiniteBitVecState dimension).memaddrs
          bitAddress = true)
      state.be (holWordToBitVec dimension address)).map
        (fun byte => PanWordLab.word
          (BitVec.ofNat dimension.width byte.toNat)) := by
  exact evalCrepHolFiniteWordSourceExpWordLab_loadByte_eq_panMemLoadByteHOL
    dimension state.toSourceEvaluatorState addressExpression address hAddress

/-- Arbitrary-index finite-state `Op` case of HOL `eval_def`. The successful
`mapM` result is the recursive induction information; the result is exactly
the tagged `word_op_def` operation after the word-index conversion and keeps
the full `word_lab` wrapper. The enclosing evaluator still uses the explicit
dimension projection, so this case is not tagged as native `eval_def`. -/
theorem evalCrepHolFiniteStateSource_op
    {ι β σ : Type} [dimension : HolFiniteDimension ι]
    (state : CrepSemHOLFiniteState ι β σ) (operator : BinOp)
    (expressions : List (CrepExp (ι → Bool))) (values : List (ι → Bool))
    (hValues : expressions.mapM
      (evalCrepHolFiniteWordSourceExp dimension
        state.toSourceEvaluatorState) = some values) :
    (evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState (.op operator expressions)).map
        (mapCrepHolWordLab (holWordToBitVec dimension)) =
    (wordOpHOL operator (values.map (holWordToBitVec dimension))).map
      PanWordLab.word := by
  exact evalCrepHolFiniteWordSourceExpWordLab_op_eq_wordOpHOL
    dimension state.toSourceEvaluatorState operator expressions values hValues

/-- Arbitrary-index finite-state `CrepOp.mul` case of HOL `eval_def`. Its
successful child premises reproduce the recursive evaluator case, and the
result is the tagged `crep_op_def` operation with the complete `word_lab`
wrapper. This remains untagged because it is still a clause of the explicit
dimension source evaluator, not the complete native HOL evaluator. -/
theorem evalCrepHolFiniteStateSource_crepOpMul
    {ι β σ : Type} [dimension : HolFiniteDimension ι]
    (state : CrepSemHOLFiniteState ι β σ)
    (left right : CrepExp (ι → Bool)) (leftValue rightValue : ι → Bool)
    (hLeft : evalCrepHolFiniteWordSourceExp dimension
      state.toSourceEvaluatorState left = some leftValue)
    (hRight : evalCrepHolFiniteWordSourceExp dimension
      state.toSourceEvaluatorState right = some rightValue) :
    (evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState (.crepOp .mul [left, right])).map
        (mapCrepHolWordLab (holWordToBitVec dimension)) =
    (crepOpCrepWord (width := dimension.width) .mul
      [holWordToBitVec dimension leftValue,
       holWordToBitVec dimension rightValue]).map PanWordLab.word := by
  exact evalCrepHolFiniteWordSourceExpWordLab_crepOp_eq_crepOpCrepWord
    dimension state.toSourceEvaluatorState left right leftValue rightValue
    hLeft hRight

/-- Arbitrary-index finite-state `Cmp` case of HOL `eval_def`. The recursive
operand results feed the exact tagged HOL `word_cmp` operation; the result
retains both finite-dimension transport and the complete `word_lab` wrapper.
This remains untagged because it is a case of the explicit-dimension source
evaluator, not yet a theorem about native HOL `crepSem$eval`. -/
theorem evalCrepHolFiniteStateSource_cmp
    {ι β σ : Type} [dimension : HolFiniteDimension ι]
    (state : CrepSemHOLFiniteState ι β σ) (operator : Cmp)
    (left right : CrepExp (ι → Bool)) (leftValue rightValue : ι → Bool)
    (hLeft : evalCrepHolFiniteWordSourceExp dimension
      state.toSourceEvaluatorState left = some leftValue)
    (hRight : evalCrepHolFiniteWordSourceExp dimension
      state.toSourceEvaluatorState right = some rightValue) :
    ((evalCrepHolFiniteWordSourceExp dimension state.toSourceEvaluatorState
      (.cmp operator left right)).map PanWordLab.word).map
        (mapCrepHolWordLab (holWordToBitVec dimension)) =
    some (PanWordLab.word
      (Compiler.Encoders.Asm.wordCmpResultHOL operator
        (holWordToBitVec dimension leftValue)
        (holWordToBitVec dimension rightValue))) := by
  exact evalCrepHolFiniteWordSourceExpWordLab_cmp_eq_wordCmpHOL
    dimension state.toSourceEvaluatorState operator left right leftValue rightValue
    hLeft hRight

/-- Arbitrary-index finite-state `Shift` case of HOL `eval_def`. It exposes
the exact tagged `word_sh` option result, including out-of-range failure, and
keeps the `word_lab` constructor around any successful result. It is not
tagged as native `eval_def` while the explicit-dimension evaluator relation is
still unproved. -/
theorem evalCrepHolFiniteStateSource_shift
    {ι β σ : Type} [dimension : HolFiniteDimension ι]
    (state : CrepSemHOLFiniteState ι β σ) (operator : Shift)
    (left right : CrepExp (ι → Bool)) (leftValue rightValue : ι → Bool)
    (hLeft : evalCrepHolFiniteWordSourceExp dimension
      state.toSourceEvaluatorState left = some leftValue)
    (hRight : evalCrepHolFiniteWordSourceExp dimension
      state.toSourceEvaluatorState right = some rightValue) :
    ((evalCrepHolFiniteWordSourceExp dimension state.toSourceEvaluatorState
      (.shift operator left right)).map PanWordLab.word).map
        (mapCrepHolWordLab (holWordToBitVec dimension)) =
    (wordShiftHOL operator
      (holWordToBitVec dimension leftValue)
      (holWordToBitVec dimension rightValue).toNat).map PanWordLab.word := by
  exact evalCrepHolFiniteWordSourceExpWordLab_shift_eq_wordShiftHOL
    dimension state.toSourceEvaluatorState operator left right leftValue rightValue
    hLeft hRight

/-- Production-runtime all-positive-width `simp_exp_correct1` support over the
HOL-shaped state carrier and exact HOL expression syntax. The evaluator in
the premise and conclusion is `evalCrepRuntimeExp`; the source state is
projected to its expression-observable fields and then represented by the
canonical `Fin width` word model. This remains untagged because that
projection fixes code/FFI observations and does not establish the native HOL
state/evaluator or arbitrary `finite_index` correspondence. -/
theorem crepSimpExpCorrect1CrepSemHOLStateRuntime
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ)
    (expression : CrepExpHOL width)
    (_result : HolWordLab width)
    (h : (evalCrepRuntimeExp
      state.toExpressionEvaluatorState.toHolWordBitsRuntime
      (crepExpHOLToSourceBits expression)).map PanWordLab.word ≠ none) :
    (evalCrepRuntimeExp
      (state.mapc update).toExpressionEvaluatorState.toHolWordBitsRuntime
      (crepSimpExp
        (fun n => bitVecToHolWordBits (BitVec.ofNat width n))
        (crepExpHOLToSourceBits expression))).map PanWordLab.word =
    (evalCrepRuntimeExp
      state.toExpressionEvaluatorState.toHolWordBitsRuntime
      (crepExpHOLToSourceBits expression)).map PanWordLab.word := by
  rw [CrepSemHOLState.toExpressionEvaluatorState_mapc]
  let projected := state.toExpressionEvaluatorState
  have hCodeId :
      crepArithHolWordBitsMapCode
        (fun pair : FunName × (List Nat × CrepProg (Fin width → Bool)) => pair.2)
        projected = projected := by
    cases projected
    simp [crepArithHolWordBitsMapCode]
  have hPres := crepSimpExpCorrect1HolWordBits
    (f := fun pair : FunName × (List Nat × CrepProg (Fin width → Bool)) => pair.2)
    projected (crepExpHOLToSourceBits expression) h
  rw [hCodeId] at hPres
  exact hPres

/-- Direct BitVec production-runtime support for all-positive-width
`crepSemHOLState`. It takes HOL's exact `CrepExpHOL` input and `HolWordLab`
result carrier, and applies the actual HOL-shaped `mapc` update. The evaluator
uses the production RISC-V runtime on a direct word-cell projection, so no
`Fin width → Bool` conversion occurs here. It remains untagged: code/FFI are
fixed in the expression-only projection, and the generic HOL
finite-index/eval_def relation is not established. -/
theorem crepSimpExpCorrect1CrepSemHOLStateBitVecRuntime
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ)
    (expression : CrepExpHOL width)
    (_result : HolWordLab width)
    (h : ((evalCrepRuntimeExp
      (riscvCrepWordTarget state.toBitVecEvaluatorState.toRuntime)
      (crepExpOfHOL expression)).map PanWordLab.word).map
        PanWordLab.toHolWordLab ≠ none) :
    ((evalCrepRuntimeExp
      (riscvCrepWordTarget
        (state.mapc update).toBitVecEvaluatorState.toRuntime)
      (crepSimpExp (BitVec.ofNat width) (crepExpOfHOL expression))).map
        PanWordLab.word).map PanWordLab.toHolWordLab =
    ((evalCrepRuntimeExp
      (riscvCrepWordTarget state.toBitVecEvaluatorState.toRuntime)
      (crepExpOfHOL expression)).map PanWordLab.word).map
        PanWordLab.toHolWordLab := by
  rw [CrepSemHOLState.toBitVecEvaluatorState_mapc]
  let projected := state.toBitVecEvaluatorState
  let productionExpression := crepExpOfHOL expression
  have hRuntime :
      (evalCrepRuntimeExp (riscvCrepWordTarget projected.toRuntime)
        productionExpression).map PanWordLab.word ≠ none := by
    have hWrapped := h
    change ((evalCrepRuntimeExp (riscvCrepWordTarget projected.toRuntime)
      productionExpression).map PanWordLab.word).map PanWordLab.toHolWordLab ≠ none
      at hWrapped
    intro hnone
    rw [hnone] at hWrapped
    simp at hWrapped
  have hSource :
      evalCrepHolExpWordLab projected productionExpression ≠ none := by
    rw [evalCrepHolExpWordLab, ← evalCrepRuntimeExp_toRuntime_eq]
    exact hRuntime
  have hCodeId :
      crepArithHolMapCode
        (fun pair : FunName × (List Nat × CrepProg (RiscV.Word width)) => pair.2)
        projected = projected := by
    cases projected
    simp [crepArithHolMapCode]
  have hPres := crepSimpExpCorrect1BitVec
    (f := fun pair : FunName × (List Nat × CrepProg (RiscV.Word width)) => pair.2)
    projected productionExpression hSource
  rw [hCodeId] at hPres
  have hRuntimePreserved :
      (evalCrepRuntimeExp (riscvCrepWordTarget projected.toRuntime)
        (crepSimpExp (BitVec.ofNat width) productionExpression)).map
          PanWordLab.word =
      (evalCrepRuntimeExp (riscvCrepWordTarget projected.toRuntime)
        productionExpression).map PanWordLab.word := by
    calc
      _ = evalCrepHolExpWordLab projected
            (crepSimpExp (BitVec.ofNat width) productionExpression) := by
              simp only [evalCrepHolExpWordLab]
              rw [evalCrepRuntimeExp_toRuntime_eq]
      _ = evalCrepHolExpWordLab projected productionExpression := hPres
      _ = _ := by
            simp only [evalCrepHolExpWordLab]
            rw [evalCrepRuntimeExp_toRuntime_eq]
  exact congrArg (Option.map PanWordLab.toHolWordLab) hRuntimePreserved

/-- All-positive-width `simp_exp_correct1` support over the exact
`CrepSemHOLState` and `CrepExpHOL` carriers, using the source-shaped
`evalCrepHolExp` translation of `crepSem$eval_def` in the premise and result.
The code update has HOL's exact `MlString`/`CrepProgHOL` type and the result
preserves the complete `HolWordLab`-backed word result through the evaluator's
word-lab projection. This stays untagged because the source evaluator still
uses canonical `BitVec width` rather than an arbitrary HOL finite_index
carrier; the adjacent production-runtime theorem separately connects this
result to the executed evaluator. -/
theorem crepSimpExpCorrect1CrepSemHOLStateHolEval
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ)
    (expression : CrepExpHOL width)
    (_result : HolWordLab width)
    (h : evalCrepHolExpWordLab state.toBitVecEvaluatorState
      (crepExpOfHOL expression) ≠ none) :
    evalCrepHolExpWordLab
      (state.mapc update).toBitVecEvaluatorState
      (crepSimpExp (BitVec.ofNat width) (crepExpOfHOL expression)) =
    evalCrepHolExpWordLab state.toBitVecEvaluatorState
      (crepExpOfHOL expression) := by
  rw [CrepSemHOLState.toBitVecEvaluatorState_mapc]
  let projected := state.toBitVecEvaluatorState
  have hCodeId :
      crepArithHolMapCode
        (fun pair : FunName × (List Nat × CrepProg (RiscV.Word width)) => pair.2)
        projected = projected := by
    cases projected
    simp [crepArithHolMapCode]
  have hPres := crepSimpExpCorrect1BitVec
    (f := fun pair : FunName × (List Nat × CrepProg (RiscV.Word width)) => pair.2)
    projected (crepExpOfHOL expression) h
  rw [hCodeId] at hPres
  exact hPres

/-- Var case of HOL `simp_exp_correct1` (`crep_arithProofScript.sml:111`). It
    retains the successful-evaluation premise, polymorphic unused result
    binder, full `Option (word_lab)` result and proof-script-local code-only
    `mapc` update. The same-module finite-map witness above re-exports the
    existing `CrepSemHOLState` roundtrip; it does not declare a second carrier. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct1"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrect1NativeVarCase
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (name : Nat)
    {resultType : Type} (_result : resultType)
    (_h : evalCrepSemHOLExp state (.var name) ≠ none) :
    evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
        (crepSimpExpHOL (.var name)) =
      evalCrepSemHOLExp state (.var name) := by
  simp only [CrepSemHOLState.mapc, crepSimpExpHOL, evalCrepSemHOLExp]

/-- Const case of HOL `simp_exp_correct1` (`crep_arithProofScript.sml:111`). It
    preserves the same premise and polymorphic unused result binder, plus the
    complete optional `word_lab` conclusion; a constant evaluates to the same
    word after the code-only `mapc` update. The state finite-map fields use the
    reviewed canonical finite-support carrier, and words use the reviewed
    positive-width `BitVec` model. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct1"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrect1NativeConstCase
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (value : BitVec width)
    {resultType : Type} (_result : resultType)
    (_h : evalCrepSemHOLExp state (.const value) ≠ none) :
    evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
        (crepSimpExpHOL (.const value)) =
      evalCrepSemHOLExp state (.const value) := by
  simp only [CrepSemHOLState.mapc, crepSimpExpHOL, evalCrepSemHOLExp]

/-- LoadGlob case of HOL `simp_exp_correct1` (`crep_arithProofScript.sml:111`).
    HOL `eval_def` reads the globals finite map, while the proof-script-local
    `mapc` update changes only code; `simp_exp` leaves LoadGlob unchanged.
    The theorem keeps the unused polymorphic result binder, successful
    evaluation premise, and complete optional `word_lab` result. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct1"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrect1NativeLoadGlobCase
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (address : BitVec 5)
    {resultType : Type} (_result : resultType)
    (_h : evalCrepSemHOLExp state (.loadGlob address) ≠ none) :
    evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
        (crepSimpExpHOL (.loadGlob address)) =
      evalCrepSemHOLExp state (.loadGlob address) := by
  simp only [CrepSemHOLState.mapc, crepSimpExpHOL, evalCrepSemHOLExp]

/-- BaseAddr case of HOL `simp_exp_correct1` (`crep_arithProofScript.sml:111`).
    HOL `eval_def` reads `state.base_addr`, `simp_exp` leaves BaseAddr
    unchanged, and the proof-script-local `mapc` update changes only code.
    The theorem preserves the unused polymorphic result binder, successful
    evaluation premise, and complete optional `word_lab` result. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct1"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrect1NativeBaseAddrCase
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ)
    {resultType : Type} (_result : resultType)
    (_h : evalCrepSemHOLExp state .baseAddr ≠ none) :
    evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
        (crepSimpExpHOL .baseAddr) =
      evalCrepSemHOLExp state .baseAddr := by
  simp only [CrepSemHOLState.mapc, crepSimpExpHOL, evalCrepSemHOLExp]

/-- TopAddr case of HOL `simp_exp_correct1` (`crep_arithProofScript.sml:111`).
    HOL `eval_def` reads `state.top_addr`, `simp_exp` leaves TopAddr
    unchanged, and the proof-script-local `mapc` update changes only code.
    The theorem preserves the unused polymorphic result binder, successful
    evaluation premise, and complete optional `word_lab` result. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct1"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrect1NativeTopAddrCase
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ)
    {resultType : Type} (_result : resultType)
    (_h : evalCrepSemHOLExp state .topAddr ≠ none) :
    evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
        (crepSimpExpHOL .topAddr) =
      evalCrepSemHOLExp state .topAddr := by
  simp only [CrepSemHOLState.mapc, crepSimpExpHOL, evalCrepSemHOLExp]

/-- Load case of HOL `simp_exp_correct1` (`crep_arithProofScript.sml:111`).
    The recursive premise is at the same state as the Load evaluation, as in
    HOL's `eval_ind`. The successful full Load evaluation
    premise is retained; code-only `mapc` preserves evaluation of the address,
    and the complete optional `word_lab` result is unchanged. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct1"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrect1NativeLoadCase
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (address : CrepExpHOL width)
    {resultType : Type} (_result : resultType)
    (_h : evalCrepSemHOLExp state (.load address) ≠ none)
    (ih : ∀ {resultType : Type} (_result : resultType),
      evalCrepSemHOLExp state address ≠ none →
      evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
          (crepSimpExpHOL address) =
        evalCrepSemHOLExp state address) :
    evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
        (crepSimpExpHOL (.load address)) =
      evalCrepSemHOLExp state (.load address) := by
  have hAddress : evalCrepSemHOLExp state address ≠ none := by
    intro hNone
    apply _h
    simp [evalCrepSemHOLExp, hNone]
  have hAddressEval := ih _result hAddress
  simp only [crepSimpExpHOL]
  simp only [evalCrepSemHOLExp]
  rw [hAddressEval]
  rfl

/-- Load32 case of HOL `simp_exp_correct1` (`crep_arithProofScript.sml:111`).
    The recursive premise uses the current state, as in HOL `eval_ind`, and
    retains the unused result binder. The successful full Load32 premise,
    exact code-only `mapc`, and complete optional `word_lab` result are kept. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct1"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrect1NativeLoad32Case
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (address : CrepExpHOL width)
    {resultType : Type} (_result : resultType)
    (_h : evalCrepSemHOLExp state (.load32 address) ≠ none)
    (ih : ∀ {resultType : Type} (_result : resultType),
      evalCrepSemHOLExp state address ≠ none →
      evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
          (crepSimpExpHOL address) =
        evalCrepSemHOLExp state address) :
    evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
        (crepSimpExpHOL (.load32 address)) =
      evalCrepSemHOLExp state (.load32 address) := by
  have hAddress : evalCrepSemHOLExp state address ≠ none := by
    intro hNone
    apply _h
    simp [evalCrepSemHOLExp, hNone]
  have hAddressEval := ih _result hAddress
  simp only [crepSimpExpHOL]
  simp only [evalCrepSemHOLExp]
  rw [hAddressEval]
  rfl

/-- LoadByte case of HOL `simp_exp_correct1` (`crep_arithProofScript.sml:111`).
    Its recursive premise uses the current state, as in HOL `eval_ind`, and
    retains the unused result binder. The full successful-load premise,
    code-only `mapc`, and complete optional `word_lab` result are retained. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct1"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrect1NativeLoadByteCase
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (address : CrepExpHOL width)
    {resultType : Type} (_result : resultType)
    (_h : evalCrepSemHOLExp state (.loadByte address) ≠ none)
    (ih : ∀ {resultType : Type} (_result : resultType),
      evalCrepSemHOLExp state address ≠ none →
      evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
          (crepSimpExpHOL address) =
        evalCrepSemHOLExp state address) :
    evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
        (crepSimpExpHOL (.loadByte address)) =
      evalCrepSemHOLExp state (.loadByte address) := by
  have hAddress : evalCrepSemHOLExp state address ≠ none := by
    intro hNone
    apply _h
    simp [evalCrepSemHOLExp, hNone]
  have hAddressEval := ih _result hAddress
  simp only [crepSimpExpHOL]
  simp only [evalCrepSemHOLExp]
  rw [hAddressEval]
  rfl

/-- Cmp case of HOL `simp_exp_correct1` (`crep_arithProofScript.sml:111`).
    Both child induction hypotheses use the current state, as in HOL
    `eval_ind`, while retaining the unused result binder. The successful
    full-Cmp premise, code-only `mapc`, and complete optional result remain. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct1"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrect1NativeCmpCase
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (operator : Cmp)
    (left right : CrepExpHOL width)
    {resultType : Type} (_result : resultType)
    (_h : evalCrepSemHOLExp state (.cmp operator left right) ≠ none)
    (ihLeft : ∀ {resultType : Type} (_result : resultType),
      evalCrepSemHOLExp state left ≠ none →
      evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
          (crepSimpExpHOL left) = evalCrepSemHOLExp state left)
    (ihRight : ∀ {resultType : Type} (_result : resultType),
      evalCrepSemHOLExp state right ≠ none →
      evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
          (crepSimpExpHOL right) = evalCrepSemHOLExp state right) :
    evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
        (crepSimpExpHOL (.cmp operator left right)) =
      evalCrepSemHOLExp state (.cmp operator left right) := by
  have hLeft : evalCrepSemHOLExp state left ≠ none := by
    intro hNone
    apply _h
    simp [evalCrepSemHOLExp, hNone]
  have hRight : evalCrepSemHOLExp state right ≠ none := by
    intro hNone
    apply _h
    simp [evalCrepSemHOLExp, hNone]
  have hLeftEval := ihLeft _result hLeft
  have hRightEval := ihRight _result hRight
  simp only [crepSimpExpHOL]
  simp only [evalCrepSemHOLExp]
  rw [hLeftEval, hRightEval]

/-- Shift case of HOL `simp_exp_correct1` (`crep_arithProofScript.sml:111`).
    Both child induction hypotheses use the current state, as in HOL
    `eval_ind`, while retaining the unused result binder. The successful
    full-Shift premise, code-only `mapc`, and complete optional result remain. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct1"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrect1NativeShiftCase
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (operator : Shift)
    (left right : CrepExpHOL width)
    {resultType : Type} (_result : resultType)
    (_h : evalCrepSemHOLExp state (.shift operator left right) ≠ none)
    (ihLeft : ∀ {resultType : Type} (_result : resultType),
      evalCrepSemHOLExp state left ≠ none →
      evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
          (crepSimpExpHOL left) = evalCrepSemHOLExp state left)
    (ihRight : ∀ {resultType : Type} (_result : resultType),
      evalCrepSemHOLExp state right ≠ none →
      evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
          (crepSimpExpHOL right) = evalCrepSemHOLExp state right) :
    evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
        (crepSimpExpHOL (.shift operator left right)) =
      evalCrepSemHOLExp state (.shift operator left right) := by
  have hLeft : evalCrepSemHOLExp state left ≠ none := by
    intro hNone
    apply _h
    simp [evalCrepSemHOLExp, hNone]
  have hRight : evalCrepSemHOLExp state right ≠ none := by
    intro hNone
    apply _h
    simp [evalCrepSemHOLExp, hNone]
  have hLeftEval := ihLeft _result hLeft
  have hRightEval := ihRight _result hRight
  simp only [crepSimpExpHOL]
  simp only [evalCrepSemHOLExp]
  rw [hLeftEval, hRightEval]

/-- Op case of HOL `simp_exp_correct1` (`crep_arithProofScript.sml:111`), where
    `simp_exp (Op bop exps) = Op bop (MAP simp_exp exps)`
    (`crep_arithScript.sml:75`).  The operand-list induction hypothesis is
    HOL `eval_ind`'s Op premise at the current state (`∀e. MEM e es ⇒ P s e`)
    and keeps HOL's unused result binder.  The successful full-expression
    premise, code-only `mapc`, and complete optional `word_lab` result are
    retained; the proof lifts the per-operand equalities through `OPT_MMAP`
    with `OPT_MMAP_EQ_SOME_MONO` (`optMmapEqSomeMono`), as HOL does. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct1"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrect1NativeOpCase
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (operator : BinOp)
    (expressions : List (CrepExpHOL width))
    {resultType : Type} (_result : resultType)
    (_h : evalCrepSemHOLExp state (.op operator expressions) ≠ none)
    (ih : ∀ (child : CrepExpHOL width), child ∈ expressions →
      ∀ {resultType : Type} (_result : resultType),
        evalCrepSemHOLExp state child ≠ none →
        evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
            (crepSimpExpHOL child) = evalCrepSemHOLExp state child) :
    evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
        (crepSimpExpHOL (.op operator expressions)) =
      evalCrepSemHOLExp state (.op operator expressions) := by
  have hArgsSome : expressions.mapM (evalCrepSemHOLExp state) ≠ none := by
    intro hNone
    apply _h
    rw [evalCrepSemHOLExp.eq_7, hNone]
    rfl
  obtain ⟨values, hArgs⟩ := Option.ne_none_iff_exists'.mp hArgsSome
  have hSimplifiedArgs := optMmapEqSomeMono
    (evalCrepSemHOLExp state)
    (fun child => evalCrepSemHOLExp
      (CrepSemHOLState.mapc update state) (crepSimpExpHOL child))
    expressions values hArgs
    (by
      intro child value hmem hValue
      have hChildIH := ih child hmem _result (by rw [hValue]; simp)
      rw [hChildIH, hValue])
  have hSimplifiedArgs' :
      (expressions.map crepSimpExpHOL).mapM
          (evalCrepSemHOLExp (CrepSemHOLState.mapc update state)) = some values := by
    rw [List.mapM_map]
    exact hSimplifiedArgs
  have hSimplified :
      crepSimpExpHOL (.op operator expressions) =
        .op operator (expressions.map crepSimpExpHOL) := by
    simp only [crepSimpExpHOL]
  rw [hSimplified, evalCrepSemHOLExp.eq_7, evalCrepSemHOLExp.eq_7,
    hSimplifiedArgs', hArgs]

/-- Flapjack-only inversion lemma for the exact `dest_const` function. HOL's
    proof script invokes the analogous standard HOL equality reasoning
    directly; this local theorem exposes the constructor inversion needed by
    Lean's indexed Crep carrier. -/
private theorem crepDestConstHOL_eq_some_implies {width : Nat} [NeZero width]
    {expression : CrepExpHOL width} {value : BitVec width}
    (h : crepDestConstHOL expression = some value) :
    expression = .const value := by
  cases expression <;> simp_all [crepDestConstHOL]

/-- Flapjack-only equation view for the Crepop/Mul recursive branch. The HOL
    simplifier equation is generated by its function definition rather than a
    separate HOL declaration; this helper uses Lean's generated equation
    theorem to expose the exact branch without unfolding recursive children. -/
private theorem crepSimpExpHOL_mul_eq {width : Nat} [NeZero width]
    (left right : CrepExpHOL width) :
    crepSimpExpHOL (.crepOp .mul [left, right]) =
      match crepDestConstHOL (crepSimpExpHOL left),
          crepDestConstHOL (crepSimpExpHOL right) with
      | some first, some second => .const (first * second)
      | some constant, none => crepMulConstHOL (crepSimpExpHOL right) constant
      | none, some constant => crepMulConstHOL (crepSimpExpHOL left) constant
      | none, none => .crepOp .mul [crepSimpExpHOL left, crepSimpExpHOL right] := by
  have hMap : List.map crepSimpExpHOL [left, right] =
      [crepSimpExpHOL left, crepSimpExpHOL right] := rfl
  rw [crepSimpExpHOL.eq_1 [left, right]
    (crepSimpExpHOL left) (crepSimpExpHOL right) hMap]
  rfl

/-- Crepop case of HOL `simp_exp_correct1` (`crep_arithProofScript.sml:111`).
    The operand-list induction hypothesis is fixed to the current state and
    keeps HOL's unused result binder. The successful full-expression premise,
    code-only `mapc`, and complete optional `word_lab` result are retained;
    the Mul constant-fold and `mul_const` cases use the exact arithmetic
    helper `eval_mul_const`. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct1"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrect1NativeCrepopCase
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (operator : CrepOp)
    (expressions : List (CrepExpHOL width))
    {resultType : Type} (_result : resultType)
    (_h : evalCrepSemHOLExp state (.crepOp operator expressions) ≠ none)
    (ih : ∀ (child : CrepExpHOL width), child ∈ expressions →
      ∀ {resultType : Type} (_result : resultType),
        evalCrepSemHOLExp state child ≠ none →
        evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
            (crepSimpExpHOL child) = evalCrepSemHOLExp state child) :
    evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
        (crepSimpExpHOL (.crepOp operator expressions)) =
      evalCrepSemHOLExp state (.crepOp operator expressions) := by
  cases operator with
  | mul =>
    cases expressions with
    | nil =>
      have hEval : evalCrepSemHOLExp state (.crepOp .mul []) = none := by
        simp [evalCrepSemHOLExp, crepOpCrepWord]
      exact (False.elim (_h hEval))
    | cons left rest =>
      cases rest with
      | nil =>
        have hEval : evalCrepSemHOLExp state (.crepOp .mul [left]) = none := by
          cases hLeft : evalCrepSemHOLExp state left <;>
            simp [evalCrepSemHOLExp, hLeft, crepOpCrepWord]
        exact (False.elim (_h hEval))
      | cons right tail =>
        cases tail with
        | cons extra more =>
          have hEval :
              evalCrepSemHOLExp state (.crepOp .mul (left :: right :: extra :: more)) = none := by
            cases hLeft : evalCrepSemHOLExp state left <;>
              cases hRight : evalCrepSemHOLExp state right <;>
              cases hExtra : evalCrepSemHOLExp state extra <;>
              cases hMore : more.mapM (evalCrepSemHOLExp state) <;>
                simp [evalCrepSemHOLExp, hLeft, hRight, hExtra, hMore, crepOpCrepWord]
          exact (False.elim (_h hEval))
        | nil =>
          have hLeft : evalCrepSemHOLExp state left ≠ none := by
            intro hNone
            apply _h
            simp [evalCrepSemHOLExp, hNone]
          have hRight : evalCrepSemHOLExp state right ≠ none := by
            intro hNone
            apply _h
            simp [evalCrepSemHOLExp, hNone]
          obtain ⟨leftResult, hLeftEval⟩ := Option.ne_none_iff_exists'.mp hLeft
          obtain ⟨rightResult, hRightEval⟩ := Option.ne_none_iff_exists'.mp hRight
          cases leftResult with
          | word leftWord =>
            cases rightResult with
            | word rightWord =>
              have hLeftIH := ih left (by simp) _result hLeft
              have hRightIH := ih right (by simp) _result hRight
              have hLeftMapped :
                  evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
                    (crepSimpExpHOL left) = some (.word leftWord) := by
                rw [hLeftIH, hLeftEval]
              have hRightMapped :
                  evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
                    (crepSimpExpHOL right) = some (.word rightWord) := by
                rw [hRightIH, hRightEval]
              have hOriginal :
                  evalCrepSemHOLExp state (.crepOp .mul [left, right]) =
                    some (.word (leftWord * rightWord)) := by
                simp [evalCrepSemHOLExp, hLeftEval, hRightEval, crepOpCrepWord]
              cases hLeftConst : crepDestConstHOL (crepSimpExpHOL left) with
              | none =>
                cases hRightConst : crepDestConstHOL (crepSimpExpHOL right) with
                | none =>
                  have hSimplified :
                      crepSimpExpHOL (.crepOp .mul [left, right]) =
                        .crepOp .mul [crepSimpExpHOL left, crepSimpExpHOL right] := by
                    rw [crepSimpExpHOL_mul_eq, hLeftConst, hRightConst]
                  rw [hSimplified]
                  have hOriginalArgs :
                      [left, right].mapM (evalCrepSemHOLExp state) =
                        some [.word leftWord, .word rightWord] := by
                    simp [hLeftEval, hRightEval]
                  have hSimplifiedArgs := optMmapEqSomeMono
                    (evalCrepSemHOLExp state)
                    (fun child => evalCrepSemHOLExp
                      (CrepSemHOLState.mapc update state) (crepSimpExpHOL child))
                    [left, right] [.word leftWord, .word rightWord] hOriginalArgs
                    (by
                      intro child value hmem hValue
                      have hChildIH := ih child hmem _result (by rw [hValue]; simp)
                      rw [hChildIH, hValue])
                  have hSimplifiedArgs' :
                      [crepSimpExpHOL left, crepSimpExpHOL right].mapM
                          (evalCrepSemHOLExp (CrepSemHOLState.mapc update state)) =
                        some [.word leftWord, .word rightWord] := by
                    simpa using hSimplifiedArgs
                  rw [evalCrepSemHOLExp.eq_8, evalCrepSemHOLExp.eq_8,
                    hSimplifiedArgs', hOriginalArgs]
                | some rightConst =>
                  have hRightConstExp :
                      crepSimpExpHOL right = .const rightConst := by
                    exact crepDestConstHOL_eq_some_implies hRightConst
                  have hRightValue : rightConst = rightWord := by
                    have hEval := hRightMapped
                    rw [hRightConstExp, evalCrepSemHOLExp] at hEval
                    injection hEval with hValue
                    cases hValue
                    rfl
                  have hMulConst := crepEval_mul_const
                    (CrepSemHOLState.mapc update state)
                    (crepSimpExpHOL left) leftWord rightConst hLeftMapped
                  have hSimplified :
                      crepSimpExpHOL (.crepOp .mul [left, right]) =
                        crepMulConstHOL (crepSimpExpHOL left) rightConst := by
                    rw [crepSimpExpHOL_mul_eq, hLeftConst, hRightConst]
                  rw [hSimplified, hMulConst, hOriginal]
                  simp [hRightValue]
              | some leftConst =>
                cases hRightConst : crepDestConstHOL (crepSimpExpHOL right) with
                | none =>
                  have hLeftConstExp :
                      crepSimpExpHOL left = .const leftConst := by
                    exact crepDestConstHOL_eq_some_implies hLeftConst
                  have hLeftValue : leftConst = leftWord := by
                    have hEval := hLeftMapped
                    rw [hLeftConstExp, evalCrepSemHOLExp] at hEval
                    injection hEval with hValue
                    cases hValue
                    rfl
                  have hMulConst := crepEval_mul_const
                    (CrepSemHOLState.mapc update state)
                    (crepSimpExpHOL right) rightWord leftConst hRightMapped
                  have hSimplified :
                      crepSimpExpHOL (.crepOp .mul [left, right]) =
                        crepMulConstHOL (crepSimpExpHOL right) leftConst := by
                    rw [crepSimpExpHOL_mul_eq, hLeftConst, hRightConst]
                  rw [hSimplified, hMulConst, hOriginal]
                  simpa [hLeftValue] using (BitVec.mul_comm rightWord leftWord)
                | some rightConst =>
                  have hLeftConstExp :
                      crepSimpExpHOL left = .const leftConst := by
                    exact crepDestConstHOL_eq_some_implies hLeftConst
                  have hRightConstExp :
                      crepSimpExpHOL right = .const rightConst := by
                    exact crepDestConstHOL_eq_some_implies hRightConst
                  have hLeftValue : leftConst = leftWord := by
                    have hEval := hLeftMapped
                    rw [hLeftConstExp, evalCrepSemHOLExp] at hEval
                    injection hEval with hValue
                    cases hValue
                    rfl
                  have hRightValue : rightConst = rightWord := by
                    have hEval := hRightMapped
                    rw [hRightConstExp, evalCrepSemHOLExp] at hEval
                    injection hEval with hValue
                    cases hValue
                    rfl
                  have hSimplified :
                      crepSimpExpHOL (.crepOp .mul [left, right]) =
                        CrepExpHOL.const (leftConst * rightConst) := by
                    rw [crepSimpExpHOL_mul_eq, hLeftConst, hRightConst]
                  rw [hSimplified]
                  rw [evalCrepSemHOLExp, hOriginal]
                  simp [hLeftValue, hRightValue]

/-- Arbitrary finite-index support over the exact HOL-shaped state/code
carriers. The state retains finite-map locals/globals/code, the HOL
`MlString`/`CrepProgHOL` code-entry type, total memory and set domains, and
`HolFfiState`; `dimension` supplies the explicit finite-index enumeration.
Expressions and word-lab results are transported between the exact
`CrepExpHOL`/`BitVec` syntax and the dimension-indexed `ι → Bool` source
evaluator. This remains untagged because that source evaluator's dimension
and word-operation adapters have not yet been proved identical to HOL's
implicit `finite_index` instances and native `crepSem$eval`. -/
theorem crepSimpExpCorrect1CrepSemHOLFiniteStateSourceEval
    {ι : Type} (dimension : HolFiniteDimension ι) {σ : Type}
    (update : MlString ×
      (List Nat × CrepProgHOL dimension.width) →
      List Nat × CrepProgHOL dimension.width)
    (state : CrepSemHOLFiniteState ι
      (List Nat × CrepProgHOL dimension.width) σ)
    (expression : CrepExpHOL dimension.width)
    (_result : PanWordLab (ι → Bool))
    (h : evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState
      (mapCrepExpWord (bitVecToHolWord dimension) (crepExpOfHOL expression)) ≠ none) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      (state.mapc update).toSourceEvaluatorState
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        (mapCrepExpWord (bitVecToHolWord dimension) (crepExpOfHOL expression))) =
    evalCrepHolFiniteWordSourceExpWordLab dimension
      state.toSourceEvaluatorState
      (mapCrepExpWord (bitVecToHolWord dimension) (crepExpOfHOL expression)) := by
  letI : HolFiniteDimension ι := dimension
  let source := state.toSourceEvaluatorState
  let sourceExpression :=
    mapCrepExpWord (bitVecToHolWord dimension) (crepExpOfHOL expression)
  have hSourceUpdate :
      crepArithHolFiniteDimensionMapCode
        (fun pair : FunName × (List Nat × CrepProg (ι → Bool)) => pair.2)
        source = source := by
    cases source with
    | mk locals globals code memory memaddrs shMemaddrs clock bigEndian ffi
        baseAddress topAddress =>
      simp [crepArithHolFiniteDimensionMapCode]
  have hPreserved := crepSimpExpCorrect1HolFiniteWordSourceEvalClass
    (dimension := dimension)
    (f := fun pair : FunName × (List Nat × CrepProg (ι → Bool)) => pair.2)
    source sourceExpression _result h
  rw [hSourceUpdate] at hPreserved
  rw [CrepSemHOLFiniteState.toSourceEvaluatorState_mapc]
  exact hPreserved

/-- Native production-evaluator `Var` case against the exact finite-map local
field in `CrepSemHOLState`, corresponding to HOL `crepSem$eval_def`
(`crepSemScript.sml:91`). The production runtime state remains arbitrary,
including its code, FFI, memory model, and byte configuration; the only
premise relates the queried local observation to this state's finite-map
lookup. No state projection or successful-evaluation premise is used, so the
equation covers both a lookup hit and a miss. This stays untagged: the HOL
state uses the positive-width `BitVec` encoding rather than an arbitrary HOL
`finite_index`, and the local observation premise is only one component of the
full state/evaluator correspondence. -/
theorem evalCrepRuntimeExp_crepSemHOLState_var
    {width : Nat} [NeZero width] {σ ρ : Type}
    (holState : CrepSemHOLState width σ)
    (runtimeState : CrepRuntimeState (RiscV.Word width) ρ)
    (name : Nat)
    (hLocal : runtimeState.locals name =
      (holState.locals.lookup name).map HolWordLab.toPanWordLab) :
    ((evalCrepRuntimeExp runtimeState (.var name)).map PanWordLab.word).map
      PanWordLab.toHolWordLab = holState.locals.lookup name := by
  simp only [evalCrepRuntimeExp]
  rw [hLocal]
  cases h : holState.locals.lookup name with
  | none => simp
  | some cell => cases cell <;> simp [HolWordLab.toPanWordLab,
      PanWordLab.toHolWordLab, panTheWord]

/-- Native production-evaluator `LoadGlob` case against the exact finite-map
global field in `CrepSemHOLState`, corresponding to HOL
`crepSem$eval_def` (`crepSemScript.sml:111`). The production runtime state
remains arbitrary, including its code, FFI, memory model, and byte
configuration; the only premise relates the queried global observation to
this state's finite-map lookup. No state projection or successful-evaluation
premise is used, so the equation covers both a lookup hit and a miss. The
direct HOL rows are `eval_global_hit` and `eval_global_miss` in
`scripts/hol-probes/crep_eval_probe.out`. This stays untagged: the HOL state
uses the positive-width `BitVec` encoding rather than an arbitrary HOL
`finite_index`, and the local observation premise is only one component of the
full state/evaluator correspondence. -/
theorem evalCrepRuntimeExp_crepSemHOLState_loadGlob
    {width : Nat} [NeZero width] {σ ρ : Type}
    (holState : CrepSemHOLState width σ)
    (runtimeState : CrepRuntimeState (RiscV.Word width) ρ)
    (address : BitVec 5)
    (hGlobal : runtimeState.globals address =
      (holState.globals.lookup address).map HolWordLab.toPanWordLab) :
    ((evalCrepRuntimeExp runtimeState (.loadGlob address)).map
      PanWordLab.word).map PanWordLab.toHolWordLab =
        holState.globals.lookup address := by
  simp only [evalCrepRuntimeExp]
  rw [hGlobal]
  cases h : holState.globals.lookup address with
  | none => simp
  | some cell => cases cell <;> simp [HolWordLab.toPanWordLab,
      PanWordLab.toHolWordLab, panTheWord]

/-- Exact finite-map `Var` case for the production evaluator instantiated at
the direct BitVec projection of one `CrepSemHOLState`. This is the positive
width Lean carrier's `eval_def` case; it remains untagged because the state
word is represented by BitVec rather than HOL's arbitrary `finite_index`. -/
theorem evalCrepRuntimeExp_toBitVecEvaluatorState_var
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (name : Nat) :
    ((evalCrepRuntimeExp (state.toBitVecEvaluatorState.toRuntime)
      (.var name)).map PanWordLab.word).map PanWordLab.toHolWordLab =
      state.locals.lookup name := by
  apply evalCrepRuntimeExp_crepSemHOLState_var
  change state.toBitVecEvaluatorState.locals name = _
  rfl

/-- Exact finite-map `LoadGlob` case for the production evaluator at the
direct BitVec projection of one `CrepSemHOLState`; kept untagged for the same
arbitrary-`finite_index` reason as the `Var` case. -/
theorem evalCrepRuntimeExp_toBitVecEvaluatorState_loadGlob
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (address : BitVec 5) :
    ((evalCrepRuntimeExp (state.toBitVecEvaluatorState.toRuntime)
      (.loadGlob address)).map PanWordLab.word).map PanWordLab.toHolWordLab =
      state.globals.lookup address := by
  apply evalCrepRuntimeExp_crepSemHOLState_loadGlob
  change state.toBitVecEvaluatorState.globals address = _
  rfl


/-! ## Assembled `simp_exp_correct1` and `simp_exp_correct`

HOL proves `simp_exp_correct1` by `ho_match_mp_tac (name_ind_cases [] eval_ind)`
(`crep_arithProofScript.sml:111-142`).  Crep's expression `eval_ind` is not
ported as a Lean declaration, so the assembly below uses structural induction
on `CrepExpHOL` (with the operand-list motive `∀ child ∈ es, P child`).  This
supplies exactly the `eval_ind` IHs, all at the fixed current state, to the
twelve tagged native case theorems above. -/

/-- Exact HOL `simp_exp_correct1` (`crep_arithProofScript.sml:111-114`):
    `∀s exp v. crepSem$eval s exp ≠ NONE ⇒
      eval (mapc f s) (simp_exp exp) = eval s exp`, with `f` free (here the
    first explicit argument `update`) and HOL's unused, arbitrarily typed `v`.
    It is stated over the tagged native `evalCrepSemHOLExp` (`eval_def`),
    `crepSimpExpHOL` (`simp_exp_def`) and `CrepSemHOLState.mapc`, with the
    complete `Option word_lab` result and no other premise.  Assembled from the
    tagged native constructor cases (`crepSimpExpCorrect1Native*Case`).
    (HOL marks this theorem `[local]`; it is ported because `simp_exp_correct`
    and `simp_prog_correct` depend on it.) -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct1"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrect1NativeHOL
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width) :
    ∀ (state : CrepSemHOLState width σ) (exp : CrepExpHOL width)
      {resultType : Type} (_v : resultType),
      evalCrepSemHOLExp state exp ≠ none →
      evalCrepSemHOLExp (CrepSemHOLState.mapc update state) (crepSimpExpHOL exp) =
        evalCrepSemHOLExp state exp := by
  intro state exp
  induction exp using CrepExpHOL.rec (motive_2 := fun es => ∀ child ∈ es,
      ∀ {resultType : Type} (_v : resultType),
        evalCrepSemHOLExp state child ≠ none →
        evalCrepSemHOLExp (CrepSemHOLState.mapc update state) (crepSimpExpHOL child) =
          evalCrepSemHOLExp state child) with
  | const value =>
      intro _ v h; exact crepSimpExpCorrect1NativeConstCase update state value v h
  | var name =>
      intro _ v h; exact crepSimpExpCorrect1NativeVarCase update state name v h
  | load address ih =>
      intro _ v h; exact crepSimpExpCorrect1NativeLoadCase update state address v h ih
  | load32 address ih =>
      intro _ v h; exact crepSimpExpCorrect1NativeLoad32Case update state address v h ih
  | loadByte address ih =>
      intro _ v h; exact crepSimpExpCorrect1NativeLoadByteCase update state address v h ih
  | loadGlob address =>
      intro _ v h; exact crepSimpExpCorrect1NativeLoadGlobCase update state address v h
  | op operator args ih =>
      intro _ v h; exact crepSimpExpCorrect1NativeOpCase update state operator args v h ih
  | crepOp operator args ih =>
      intro _ v h; exact crepSimpExpCorrect1NativeCrepopCase update state operator args v h ih
  | cmp operator left right ihLeft ihRight =>
      intro _ v h
      exact crepSimpExpCorrect1NativeCmpCase update state operator left right v h ihLeft ihRight
  | shift operator left right ihLeft ihRight =>
      intro _ v h
      exact crepSimpExpCorrect1NativeShiftCase update state operator left right v h
        ihLeft ihRight
  | baseAddr =>
      intro _ v h; exact crepSimpExpCorrect1NativeBaseAddrCase update state v h
  | topAddr =>
      intro _ v h; exact crepSimpExpCorrect1NativeTopAddrCase update state v h
  | nil =>
      rename_i hmem _ _ _
      cases hmem
  | cons head tail ihHead ihTail =>
      rename_i child hmem _ v h
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact ihHead v h
      · exact ihTail child hmem v h

/-- Exact HOL `simp_exp_correct` (`crep_arithProofScript.sml:143-145`):
    `crepSem$eval s exp = SOME v ⇒ eval (mapc f s) (simp_exp exp) = SOME v`,
    with `f`, `s`, `exp`, `v` free, over the same tagged native evaluator,
    simplifier and `mapc`.  Proved from `simp_exp_correct1`, as in HOL. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepSimpExpCorrectNativeHOL
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (exp : CrepExpHOL width) (v : HolWordLab width) :
    evalCrepSemHOLExp state exp = some v →
    evalCrepSemHOLExp (CrepSemHOLState.mapc update state) (crepSimpExpHOL exp) = some v := by
  intro h
  rw [crepSimpExpCorrect1NativeHOL update state exp v (by rw [h]; simp), h]


/-- Exact HOL `opt_mmap_simp_exp_correct` (`crep_arithProofScript.sml:150-152`):
    `OPT_MMAP (crepSem$eval s) es = SOME vs ⇒
      OPT_MMAP (eval (mapc f s)) (MAP simp_exp es) = SOME vs`, with `f s es vs`
    free.  HOL `OPT_MMAP` is `List.mapM`, over the tagged native
    `evalCrepSemHOLExp`, `crepSimpExpHOL` and `CrepSemHOLState.mapc`.  Proved
    from `simp_exp_correct` elementwise, as HOL does with `OPT_MMAP_CONG`. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "opt_mmap_simp_exp_correct"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepOptMmapSimpExpCorrectNativeHOL
    {width : Nat} [NeZero width] {σ : Type}
    (update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width σ) (es : List (CrepExpHOL width))
    (vs : List (HolWordLab width)) :
    es.mapM (evalCrepSemHOLExp state) = some vs →
    (es.map crepSimpExpHOL).mapM
        (evalCrepSemHOLExp (CrepSemHOLState.mapc update state)) = some vs := by
  intro h
  rw [List.mapM_map]
  exact optMmapEqSomeMono (evalCrepSemHOLExp state) _ es vs h
    (fun child value _ hValue =>
      crepSimpExpCorrectNativeHOL update state child value hValue)

end Flapjack
