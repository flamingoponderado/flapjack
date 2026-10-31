import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ByteCopy

/-! In-place byte XOR correspondence for closure-to-BVL. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL

/-- A successful XOR has a mutable byte-array destination and an equally
long source byte vector. -/
theorem xorByte_success {C F : Type} (args : List ClosSem.Value)
    (s next : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.doApp (.memOp .xorByte) args s = .val (value, next)) :
    ∃ (flag : Bool) (ptr : Nat) (source old result : List (BitVec 8)),
      args = [.refPtr flag ptr, .byteVector source] ∧ s.refs.lookup ptr = some (.byteArray old) ∧
      xorBytes source old = some result ∧ value = ClosSem.unitValue ∧
      next = { s with refs := s.refs.updateEq (ptr, .byteArray result) } := by
  cases args with
  | nil => simp [ClosSem.doApp, ClosSem.applyMemory] at run
  | cons first rest =>
    cases rest with
    | nil => simp [ClosSem.doApp, ClosSem.applyMemory] at run
    | cons second rest =>
      cases rest with
      | cons third rest => simp [ClosSem.doApp, ClosSem.applyMemory] at run
      | nil =>
        cases first <;> cases second <;> simp only [ClosSem.doApp, ClosSem.applyMemory] at run
        all_goals try contradiction
        case refPtr.byteVector flag ptr source =>
          cases found : s.refs.lookup ptr with
          | none => simp [found] at run
          | some cell =>
            cases cell with
            | valueArray values => simp [found] at run
            | thunk mode value => simp [found] at run
            | byteArray old =>
              cases xored : xorBytes source old with
              | none => simp [found, xored] at run
              | some result =>
                simp [found, xored] at run
                exact ⟨flag, ptr, source, old, result, rfl, found, xored, run.1.symm, run.2.symm⟩

/-- XOR writes the same bytes into related mutable destination arrays. -/
theorem xorByte_dispatch {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (args : List ClosSem.Value) (targets : List BvlSem.Value)
    (s next : ClosSem.State C F) (t : BvlSem.State C F) (states : stateRel f s t)
    (related : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targets)
    (value : ClosSem.Value) (run : ClosSem.doApp (.memOp .xorByte) args s = .val (value, next)) :
    ∃ target targetNext,
      BvlSem.doApp (.memOp .xorByte) targets t = .val (target, targetNext) ∧
      stateRel f next targetNext ∧ vRel s.maxApp f targetNext.refs targetNext.code value target ∧
      unmappedRefsSubmap t.refs targetNext.refs f f ∧ next.clock = s.clock ∧ targetNext.clock = t.clock ∧
      next.code = s.code := by
  obtain ⟨flag, ptr, source, old, result, rfl, found, xored, valueEq, stateEq⟩ := xorByte_success args s next value run
  subst value
  subst next
  cases related with
  | cons dstRel tail =>
    cases tail with
    | cons sourceRel tail =>
      cases tail
      obtain ⟨targetPtr, rfl, mapped⟩ := vRel_refPtr_inv dstRel
      obtain ⟨sourcePtr, rfl, sourceFound⟩ := vRel_byteVector_inv sourceRel
      have dstFound := stateRel_bytes_lookup states ptr targetPtr old mapped found
      let targetNext := { t with refs := t.refs.updateEq (targetPtr, .byteArray false result) }
      refine ⟨BvlSem.unitValue, targetNext, ?_, ?_, .block .nil,
        mappedUpdate_frame f t.refs ptr targetPtr mapped _, rfl, rfl, rfl⟩
      · simp [BvlSem.doApp, BvlSem.applyMemory, sourceFound, dstFound, xored, targetNext]
      · exact stateRel_update_mapped s t f ptr targetPtr _ _ states mapped (by simp) ⟨rfl, rfl⟩

/-- A failed XOR reports a source type error. -/
theorem xorByte_error {C F : Type} (args : List ClosSem.Value)
    (s : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : ClosSem.doApp (.memOp .xorByte) args s = .err error) : error = .abort .typeError := by
  simp only [ClosSem.doApp] at run
  cases h : ClosSem.applyMemory .xorByte args s <;> simp [h] at run
  exact run.symm

end Flapjack.Compiler.Backend.ClosToBvl
