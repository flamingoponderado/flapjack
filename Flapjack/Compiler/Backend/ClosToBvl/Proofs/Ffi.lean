import Flapjack.Compiler.Backend.ClosToBvl.Proofs.MappedRefsUpdate

/-! Foreign-call correspondence, including observable FFI state. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL
open Flapjack.Basis.Pure.MlString

/-- Updating both FFI states to the same state preserves the candidate state
relation. -/
theorem stateRel_set_ffi {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (states : stateRel f s t) (ffi : HolFfiState F) :
    stateRel f { s with ffi := ffi } { t with ffi := ffi } := by
  exact ⟨rfl, states.2⟩

/-- A valid foreign call uses a byte-vector configuration and a mutable byte
array, and both semantics invoke the same FFI state and arguments. -/
theorem ffi_valid_related {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (states : stateRel f s t) (name : MlString)
    (config bytes : List (BitVec 8)) (configPtr : Nat) (flag : Bool) (sourcePtr targetPtr : Nat)
    (configFound : t.refs.lookup configPtr = some (.byteArray true config))
    (mapped : f.lookup sourcePtr = some targetPtr) (sourceFound : s.refs.lookup sourcePtr = some (.byteArray bytes)) :
    let result := callFFIHOL s.ffi (.extCall name) config bytes
    match result with
    | .ret ffi updated =>
      let sourceNext := { s with refs := s.refs.updateEq (sourcePtr, .byteArray updated), ffi := ffi }
      let targetNext := { t with refs := t.refs.updateEq (targetPtr, .byteArray false updated), ffi := ffi }
      ClosSem.doApp (.ffi name) [.byteVector config, .refPtr flag sourcePtr] s = .val (ClosSem.unitValue, sourceNext) ∧
      BvlSem.doApp (.ffi name) [.refPtr true configPtr, .refPtr flag targetPtr] t = .val (BvlSem.unitValue, targetNext) ∧
      stateRel f sourceNext targetNext ∧
      vRel s.maxApp f targetNext.refs targetNext.code ClosSem.unitValue BvlSem.unitValue ∧
      unmappedRefsSubmap t.refs targetNext.refs f f
    | .final event =>
      ClosSem.doApp (.ffi name) [.byteVector config, .refPtr flag sourcePtr] s = .err (.abort (.ffiError event)) ∧
      BvlSem.doApp (.ffi name) [.refPtr true configPtr, .refPtr flag targetPtr] t = .err (.abort (.ffiError event)) := by
  have targetFound := stateRel_bytes_lookup states sourcePtr targetPtr bytes mapped sourceFound
  have ffiEq : t.ffi = s.ffi := states.1.symm
  cases oracle : callFFIHOL s.ffi (.extCall name) config bytes with
  | ret ffi updated =>
    refine ⟨?_, ?_, ?_, .block .nil, mappedUpdate_frame f t.refs sourcePtr targetPtr mapped _⟩
    · simp [ClosSem.doApp, sourceFound, oracle]
    · simp [BvlSem.doApp, configFound, targetFound, ffiEq, oracle]
    · have updatedRel := stateRel_update_mapped s t f sourcePtr targetPtr (.byteArray updated)
        (.byteArray false updated) states mapped (by simp) ⟨rfl, rfl⟩
      exact stateRel_set_ffi _ _ f updatedRel ffi
  | final event =>
    exact ⟨by simp [ClosSem.doApp, sourceFound, oracle],
      by simp [BvlSem.doApp, configFound, targetFound, ffiEq, oracle]⟩

/-- Any foreign call that avoids a type error has a byte-vector
configuration and a mutable byte-array argument. -/
theorem ffi_ready {C F : Type} (name : MlString) (args : List ClosSem.Value)
    (s : ClosSem.State C F) (notType : ClosSem.doApp (.ffi name) args s ≠ .err (.abort .typeError)) :
    ∃ (config bytes : List (BitVec 8)) (flag : Bool) (ptr : Nat),
      args = [.byteVector config, .refPtr flag ptr] ∧ s.refs.lookup ptr = some (.byteArray bytes) := by
  cases args with
  | nil => simp [ClosSem.doApp] at notType
  | cons first rest =>
    cases rest with
    | nil => simp [ClosSem.doApp] at notType
    | cons second rest =>
      cases rest with
      | cons third rest => simp [ClosSem.doApp] at notType
      | nil =>
        cases first <;> cases second <;> simp only [ClosSem.doApp] at notType
        all_goals try contradiction
        case byteVector.refPtr config flag ptr =>
          cases found : s.refs.lookup ptr with
          | none => simp [found] at notType
          | some cell =>
            cases cell with
            | valueArray values => simp [found] at notType
            | thunk mode value => simp [found] at notType
            | byteArray bytes => exact ⟨config, bytes, flag, ptr, rfl, found⟩

end Flapjack.Compiler.Backend.ClosToBvl
