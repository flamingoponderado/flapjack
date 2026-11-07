import Flapjack.EvaluateProps.DoApp
import Flapjack.EvaluateProps.ClockIo

/-! Store-length prerequisites for source primitive monotonicity. The full
source evaluator and its carriers are pending review. -/
namespace Flapjack.EvaluateProps
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL

/-- Flapjack helper: a successful store assignment preserves its length. -/
theorem storeAssign_length {α : Type} (n : Nat) (value : StoreValue α) (store updated : Store α)
    (h : storeAssign n value store = some updated) : updated.length = store.length := by
  cases hget : store[n]? with
  | none => simp [storeAssign, hget] at h
  | some old =>
    simp [storeAssign, hget, bind] at h
    rcases h with ⟨_, rfl⟩
    simp

/-- Flapjack helper: successful assignment cannot shrink the store. -/
theorem storeAssign_length_le {α : Type} (n : Nat) (value : StoreValue α) (store updated : Store α)
    (h : storeAssign n value store = some updated) : store.length ≤ updated.length := by
  rw [storeAssign_length n value store updated h]
  exact Nat.le_refl _

/-- Flapjack helper: numeric primitives leave the store unchanged. -/
theorem doAppNumericCore_refs {σ : Type} (store store' : Store Value)
    (ffi ffi' : HolFfiState σ) (op : Op) (values : List Value) (result : Result Value Value)
    (h : doAppNumericCore (store, ffi) op values = some (some ((store', ffi'), result))) :
    store.length ≤ store'.length := by
  cases op <;> simp only [doAppNumericCore] at h <;>
    repeat' first | split at h | simp_all [Option.bind_eq_some_iff]
  all_goals obtain ⟨_, _, ⟨hstore, _⟩, _⟩ := h; subst store'; exact Nat.le_refl _

/-- Flapjack helper: supported basic operations do not shrink the store. -/
theorem doAppBasic_refs {σ : Type} (store store' : Store Value)
    (ffi ffi' : HolFfiState σ) (op : Op) (values : List Value) (result : Result Value Value)
    (h : doAppBasic (store, ffi) op values = some (some ((store', ffi'), result))) :
    store.length ≤ store'.length := by
  cases op <;> simp only [doAppBasic] at h <;>
    repeat' first | split at h | simp_all [Option.bind_eq_some_iff, boundsFailure, readIndexed, updateIndexed, thunkOp, storeAlloc]
  all_goals aesop (add safe storeAssign_length_le)

/-- Flapjack helper for the basic dispatcher with its default result. -/
theorem doAppBasic_getD_refs {σ : Type} (store store' : Store Value)
    (ffi ffi' : HolFfiState σ) (op : Op) (values : List Value) (result : Result Value Value)
    (h : (doAppBasic (store, ffi) op values).getD none = some ((store', ffi'), result)) :
    store.length ≤ store'.length := by
  cases hb : doAppBasic (store, ffi) op values with
  | none => simp [hb] at h
  | some outcome =>
    simp only [hb, Option.getD] at h
    apply doAppBasic_refs store store' ffi ffi' op values result
    rw [hb]
    exact congrArg some h

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "do_app_refs_length"]
theorem doApp_refs_length {σ : Type} (refsFfi : Store Value × HolFfiState σ)
    (op : Op) (values : List Value) (result : BasicAppResult σ)
    (h : doApp refsFfi op values = some result) : refsFfi.1.length ≤ result.1.1.length := by
  rcases refsFfi with ⟨store, ffi⟩
  rcases result with ⟨⟨store', ffi'⟩, result⟩
  cases op with
  | arith action typ =>
    cases typ <;> simp only [doApp, doAppBasic] at h
    case float64T =>
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨_, _, heq⟩ := h
      cases heq
      exact Nat.le_refl _
    all_goals
      split at h <;> simp_all
      apply doAppNumericCore_refs store store' ffi ffi' (.arith action _) values result
      assumption
  | test test typ =>
    simp only [doApp] at h
    repeat' first | split at h | simp_all
  | fromTo source target =>
    simp only [doApp, doAppBasic] at h
    cases hn : doAppNumericCore (store, ffi) (.fromTo source target) values with
    | none => simp [hn] at h
    | some outcome =>
      simp only [hn] at h
      apply doAppNumericCore_refs store store' ffi ffi' (.fromTo source target) values result
      rw [hn]
      exact congrArg some h
  | _ =>
    simp only [doApp, doAppNumericCore] at h
    exact doAppBasic_getD_refs store store' ffi ffi' _ values result h

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_do_app_simple"]
theorem isClockIoMono_doAppSimple {σ : Type} (op : Op) (values : List Value) (st : State σ) :
    isClockIoMono (fun state =>
      match doApp (state.refs, state.ffi) op values with
      | none => (state, Result.err (α := List Value) (.abort .typeError))
      | some ((refs, ffi), result) => ({ state with refs, ffi }, EvaluateHOL.listResult result)) st := by
  cases happ : doApp (st.refs, st.ffi) op values with
  | none =>
    simp only [isClockIoMono, happ]
    simp [ioEventsMonoHOL]
  | some output =>
    rcases output with ⟨⟨refs, ffi⟩, result⟩
    have length := doApp_refs_length (st.refs, st.ffi) op values ((refs, ffi), result) happ
    have trace := doApp_ioEventsMono st.refs refs st.ffi ffi op values result happ
    simp only [isClockIoMono, happ]
    simp [length, ioEventsMonoHOL]
    constructor
    · exact trace
    · intros
      assumption

end Flapjack.EvaluateProps
