module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.MappedRefsUpdate
public import Flapjack.SemanticPrimitivesProps.ResultRelation

@[expose] public section

/-! Foreign-call correspondence, including observable FFI state. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps
open Flapjack.Basis.Pure.MlString

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
      exact ⟨rfl, updatedRel.2⟩
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

namespace DoAppErrorCarrier
/-- Closure state finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_ClosSem.State {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- BVL state finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_BvlSem.State {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end DoAppErrorCarrier

/-- Non-type primitive errors are matched by related target errors. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "do_app_err"
  (fmap_as_finite_support_relation := [ClosSem.State.refs, ClosSem.State.code, BvlSem.State.refs, f])]
theorem doAppErr {C F : Type} (op : ClosLang.Op) (xs : List ClosSem.Value) (s1 : ClosSem.State C F)
    (err : ErrorResult ClosSem.Value) (f : HolFiniteMapExact Nat Nat) (t1 : BvlSem.State C F)
    (ys : List BvlSem.Value)
    (premises : ClosSem.doApp op xs s1 = .err err ∧ err ≠ .abort .typeError ∧
      stateRel f s1 t1 ∧ List.Forall₂ (vRel s1.maxApp f t1.refs t1.code) xs ys) :
    ∃ e, BvlSem.doApp (compileOp op) ys t1 = .err e ∧
      excRel (vRel s1.maxApp f t1.refs t1.code) err e := by
  obtain ⟨run, notType, states, related⟩ := premises
  have isFfi : ∃ name, op = .ffi name := by
    cases op
    all_goals try { exact ⟨_, rfl⟩ }
    all_goals simp only [ClosSem.doApp] at run
    all_goals repeat' split at run
    all_goals simp_all
  obtain ⟨name, rfl⟩ := isFfi
  have notTypeApp : ClosSem.doApp (.ffi name) xs s1 ≠ .err (.abort .typeError) := by
    rw [run]
    simpa using notType
  obtain ⟨config, bytes, flag, ptr, argsEq, sourceFound⟩ := ffi_ready name xs s1 notTypeApp
  subst xs
  cases related with
  | cons configRel tail =>
    cases tail with
    | cons ptrRel tail =>
      cases tail
      obtain ⟨configPtr, rfl, configFound, _⟩ := vRel_byteVector_iff.mp configRel
      obtain ⟨targetPtr, rfl, mapped⟩ := vRel_refPtr_inv ptrRel
      have valid := ffi_valid_related s1 t1 f states name config bytes configPtr flag ptr targetPtr
        configFound mapped sourceFound
      cases ffiCall : callFFIHOL s1.ffi (.extCall name) config bytes with
      | ret ffi updated =>
        rw [ffiCall] at valid
        obtain ⟨sourceApp, _, _⟩ := valid
        rw [sourceApp] at run
        contradiction
      | final event =>
        rw [ffiCall] at valid
        obtain ⟨sourceApp, targetApp⟩ := valid
        rw [sourceApp] at run
        cases run
        exact ⟨_, by simpa [compileOp] using targetApp, by simp [excRel]⟩

end Flapjack.Compiler.Backend.ClosToBvl
