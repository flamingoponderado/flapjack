import Flapjack.Compiler.Backend.ClosToBvl.Proofs.FreshMappedRefs
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.MemoryRead

/-! Updates to mapped mutable reference cells. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL

/-- Writing a mapped target cell preserves every unmapped reference. -/
theorem mappedUpdate_frame (f : HolFiniteMapExact Nat Nat)
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (sourcePtr targetPtr : Nat)
    (mapped : f.lookup sourcePtr = some targetPtr) (cell : BvlSem.Ref BvlSem.Value) :
    unmappedRefsSubmap refs (refs.updateEq (targetPtr, cell)) f f := by
  intro key value found fresh
  have ne : key ≠ targetPtr := by
    intro eq
    subst key
    exact fresh ⟨sourcePtr, mapped⟩
  exact ⟨by simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ne] using found, fresh⟩

/-- Simultaneously replacing related mapped cells preserves the candidate
state relation, with the relocation map unchanged. -/
theorem stateRel_update_mapped {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (sourcePtr targetPtr : Nat)
    (sourceCell : ClosSem.Ref ClosSem.Value) (targetCell : BvlSem.Ref BvlSem.Value)
    (states : stateRel f s t) (mapped : f.lookup sourcePtr = some targetPtr)
    (notFrozen : ∀ bytes, targetCell ≠ .byteArray true bytes)
    (cellRelated : refRel (vRel s.maxApp f (t.refs.updateEq (targetPtr, targetCell)) t.code) sourceCell targetCell) :
    stateRel f { s with refs := s.refs.updateEq (sourcePtr, sourceCell) }
      { t with refs := t.refs.updateEq (targetPtr, targetCell) } := by
  have frame := mappedUpdate_frame f t.refs sourcePtr targetPtr mapped targetCell
  have submap : relocationSubmap f f := by intro key val found; exact found
  obtain ⟨ffi, globals, table, injective, noFrozen, sourceDomain, targetDomain, cells,
    generic, partialCode, force, oracle, code⟩ := states
  have grow : ∀ a b, vRel s.maxApp f t.refs t.code a b →
      vRel s.maxApp f (t.refs.updateEq (targetPtr, targetCell)) t.code a b := by
    intro a b rel
    exact vRel_grow_refs rel submap frame
  refine ⟨ffi, ?_, table, injective, ?_, ?_, ?_, ?_, generic, partialCode, force, oracle, code⟩
  · apply globals.imp
    intro a b rel
    cases a <;> cases b <;> simp only [optionValueRel] at rel ⊢
    exact grow _ _ rel
  · intro x y bytes lookup frozen
    by_cases eq : y = targetPtr
    · subst y
      simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at frozen
      exact notFrozen bytes frozen
    · have old : t.refs.lookup y = some (.byteArray true bytes) := by
        simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq] using frozen
      exact noFrozen x y bytes lookup old
  · intro x
    by_cases eq : x = sourcePtr
    · subst x
      simp [mapped, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
    · simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq] using sourceDomain x
  · intro x y lookup
    by_cases eq : y = targetPtr
    · subst y
      simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
    · simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq] using targetDomain x y lookup
  · intro x source found
    by_cases eq : x = sourcePtr
    · subst x
      simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at found
      subst source
      exact ⟨targetCell, targetPtr, mapped, by simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL], cellRelated⟩
    · have oldFound : s.refs.lookup x = some source := by
        simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq] using found
      obtain ⟨target, ptr, lookup, targetFound, rel⟩ := cells x source oldFound
      have ptrNe : ptr ≠ targetPtr := by
        intro same
        subst ptr
        exact eq (injective x sourcePtr targetPtr lookup mapped)
      refine ⟨target, ptr, lookup, ?_, refRel_mono grow source target rel⟩
      simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ptrNe] using targetFound

/-- Writing a validated byte to corresponding mutable byte arrays preserves
the state relation and all unmapped target references. -/
theorem doApp_updateByte_related {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (states : stateRel f s t)
    (flag : Bool) (sourcePtr targetPtr : Nat) (mapped : f.lookup sourcePtr = some targetPtr)
    (bytes : List (BitVec 8)) (found : s.refs.lookup sourcePtr = some (.byteArray bytes))
    (index number : Int) (nonnegative : ¬ index < 0) (inBounds : index.toNat < bytes.length)
    (byte : BitVec 8) (valid : ClosSem.intToByte number = some byte) :
    let updated := bytes.set index.toNat byte
    let sourceNext := { s with refs := s.refs.updateEq (sourcePtr, .byteArray updated) }
    let targetNext := { t with refs := t.refs.updateEq (targetPtr, .byteArray false updated) }
    ClosSem.doApp (.memOp .updateByte) [.refPtr flag sourcePtr, .number index, .number number] s =
      .val (ClosSem.unitValue, sourceNext) ∧
    BvlSem.doApp (.memOp .updateByte) [.refPtr flag targetPtr, .number index, .number number] t =
      .val (BvlSem.unitValue, targetNext) ∧
    stateRel f sourceNext targetNext ∧
    vRel s.maxApp f targetNext.refs targetNext.code ClosSem.unitValue BvlSem.unitValue ∧
    unmappedRefsSubmap t.refs targetNext.refs f f := by
  have targetFound := stateRel_bytes_lookup states sourcePtr targetPtr bytes mapped found
  have bound : ¬ index.toNat ≥ bytes.length := by omega
  refine ⟨?_, ?_, ?_, .block .nil, mappedUpdate_frame f t.refs sourcePtr targetPtr mapped _⟩
  · simp [ClosSem.doApp, ClosSem.applyMemory, found, nonnegative, bound, valid]
  · simp [BvlSem.doApp, BvlSem.applyMemory, targetFound, nonnegative, bound, valid]
  · exact stateRel_update_mapped s t f sourcePtr targetPtr _ _ states mapped (by simp) ⟨rfl, rfl⟩

/-- Successful byte updates have the original pointer, bounds, and byte
validation conditions. -/
theorem updateByte_success {C F : Type} (args : List ClosSem.Value)
    (s next : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.doApp (.memOp .updateByte) args s = .val (value, next)) :
    ∃ (flag : Bool) (ptr : Nat) (index number : Int) (bytes : List (BitVec 8)) (byte : BitVec 8),
      args = [.refPtr flag ptr, .number index, .number number] ∧
      s.refs.lookup ptr = some (.byteArray bytes) ∧ ¬ index < 0 ∧ index.toNat < bytes.length ∧
      ClosSem.intToByte number = some byte ∧ value = ClosSem.unitValue ∧
      next = { s with refs := s.refs.updateEq (ptr, .byteArray (bytes.set index.toNat byte)) } := by
  cases args with
  | nil => simp [ClosSem.doApp, ClosSem.applyMemory] at run
  | cons first rest =>
    cases rest with
    | nil => simp [ClosSem.doApp, ClosSem.applyMemory] at run
    | cons second rest =>
      cases rest with
      | nil => simp [ClosSem.doApp, ClosSem.applyMemory] at run
      | cons third rest =>
        cases rest with
        | cons fourth rest => simp [ClosSem.doApp, ClosSem.applyMemory] at run
        | nil =>
          cases first <;> cases second <;> cases third <;> simp only [ClosSem.doApp, ClosSem.applyMemory] at run
          all_goals try contradiction
          case refPtr.number.number flag ptr index number =>
            cases found : s.refs.lookup ptr with
            | none => simp [found] at run
            | some cell =>
              cases cell with
              | valueArray values => simp [found] at run
              | thunk mode old => simp [found] at run
              | byteArray bytes =>
                by_cases negative : index < 0
                · simp [found, negative] at run
                · by_cases inBounds : index.toNat < bytes.length
                  · cases valid : ClosSem.intToByte number with
                    | none => simp [found, negative, show ¬ index.toNat ≥ bytes.length by omega, valid] at run
                    | some byte =>
                      simp [found, negative, show ¬ index.toNat ≥ bytes.length by omega, valid] at run
                      exact ⟨flag, ptr, index, number, bytes, byte, rfl, found, negative, inBounds,
                        valid, run.1.symm, run.2.symm⟩
                  · simp [found, negative, show index.toNat ≥ bytes.length by omega] at run

/-- Failed byte writes report a source type error. -/
theorem updateByte_error {C F : Type} (args : List ClosSem.Value)
    (s : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : ClosSem.doApp (.memOp .updateByte) args s = .err error) : error = .abort .typeError := by
  simp only [ClosSem.doApp] at run
  cases h : ClosSem.applyMemory .updateByte args s <;> simp [h] at run
  exact run.symm

/-- Replacing corresponding entries preserves pointwise value relations. -/
theorem relatedFields_set {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {source : List ClosSem.Value} {target : List BvlSem.Value}
    (related : List.Forall₂ (vRel maxApp f refs code) source target)
    (index : Nat) (value : ClosSem.Value) (targetValue : BvlSem.Value)
    (valueRel : vRel maxApp f refs code value targetValue) :
    List.Forall₂ (vRel maxApp f refs code) (source.set index value) (target.set index targetValue) := by
  induction related generalizing index with
  | nil => simp
  | cons head tail ih =>
    cases index with
    | zero => exact .cons valueRel tail
    | succ index => exact .cons head (ih index)

/-- Writing a related value into corresponding mutable arrays preserves the
candidate state relation and unmapped reference frame. -/
theorem doApp_updateArray_related {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (states : stateRel f s t)
    (flag : Bool) (sourcePtr targetPtr : Nat) (mapped : f.lookup sourcePtr = some targetPtr)
    (fields : List ClosSem.Value) (found : s.refs.lookup sourcePtr = some (.valueArray fields))
    (index : Int) (nonnegative : ¬ index < 0) (inBounds : index.toNat < fields.length)
    (value : ClosSem.Value) (targetValue : BvlSem.Value)
    (valueRel : vRel s.maxApp f t.refs t.code value targetValue) :
    ∃ targetFields : List BvlSem.Value,
      let sourceNext := { s with refs := s.refs.updateEq (sourcePtr, .valueArray (fields.set index.toNat value)) }
      let targetNext := { t with refs := t.refs.updateEq (targetPtr, .valueArray (targetFields.set index.toNat targetValue)) }
      ClosSem.doApp (.memOp .update) [.refPtr flag sourcePtr, .number index, value] s =
        .val (ClosSem.unitValue, sourceNext) ∧
      BvlSem.doApp (.memOp .update) [.refPtr flag targetPtr, .number index, targetValue] t =
        .val (BvlSem.unitValue, targetNext) ∧
      stateRel f sourceNext targetNext ∧
      vRel s.maxApp f targetNext.refs targetNext.code ClosSem.unitValue BvlSem.unitValue ∧
      unmappedRefsSubmap t.refs targetNext.refs f f := by
  obtain ⟨targetFields, targetFound, fieldsRel⟩ := stateRel_array_lookup states sourcePtr targetPtr fields mapped found
  let newCell := BvlSem.Ref.valueArray (targetFields.set index.toNat targetValue)
  have frame := mappedUpdate_frame f t.refs sourcePtr targetPtr mapped newCell
  have submap : relocationSubmap f f := by intro key val lookup; exact lookup
  have grownFields := fieldsRel.imp (fun _ _ rel => vRel_grow_refs rel submap frame)
  have grownValue := vRel_grow_refs valueRel submap frame
  have targetBound : ¬ index.toNat ≥ targetFields.length := by
    rw [← fieldsRel.length_eq]
    omega
  have sourceBound : ¬ index.toNat ≥ fields.length := by omega
  refine ⟨targetFields, ?_, ?_, ?_, .block .nil, frame⟩
  · simp [ClosSem.doApp, ClosSem.applyMemory, found, nonnegative, sourceBound]
  · simp [BvlSem.doApp, BvlSem.applyMemory, targetFound, nonnegative, targetBound]
  · exact stateRel_update_mapped s t f sourcePtr targetPtr _ _ states mapped (by simp)
      (relatedFields_set grownFields index.toNat value targetValue grownValue)

/-- Successful value-array writes have a valid pointer and in-bounds index. -/
theorem updateArray_success {C F : Type} (args : List ClosSem.Value)
    (s next : ClosSem.State C F) (result : ClosSem.Value)
    (run : ClosSem.doApp (.memOp .update) args s = .val (result, next)) :
    ∃ (flag : Bool) (ptr : Nat) (index : Int) (fields : List ClosSem.Value) (value : ClosSem.Value),
      args = [.refPtr flag ptr, .number index, value] ∧
      s.refs.lookup ptr = some (.valueArray fields) ∧ ¬ index < 0 ∧ index.toNat < fields.length ∧
      result = ClosSem.unitValue ∧ next = { s with refs := s.refs.updateEq (ptr, .valueArray (fields.set index.toNat value)) } := by
  cases args with
  | nil => simp [ClosSem.doApp, ClosSem.applyMemory] at run
  | cons first rest =>
    cases rest with
    | nil => simp [ClosSem.doApp, ClosSem.applyMemory] at run
    | cons second rest =>
      cases rest with
      | nil => simp [ClosSem.doApp, ClosSem.applyMemory] at run
      | cons third rest =>
        cases rest with
        | cons fourth rest => simp [ClosSem.doApp, ClosSem.applyMemory] at run
        | nil =>
          cases first <;> cases second <;> simp only [ClosSem.doApp, ClosSem.applyMemory] at run
          all_goals try contradiction
          case refPtr.number flag ptr index =>
            cases found : s.refs.lookup ptr with
            | none => simp [found] at run
            | some cell =>
              cases cell with
              | byteArray bytes => simp [found] at run
              | thunk mode old => simp [found] at run
              | valueArray fields =>
                by_cases negative : index < 0
                · simp [found, negative] at run
                · by_cases inBounds : index.toNat < fields.length
                  · simp [found, negative, show ¬ index.toNat ≥ fields.length by omega] at run
                    exact ⟨flag, ptr, index, fields, third, rfl, found, negative, inBounds, run.1.symm, run.2.symm⟩
                  · simp [found, negative, show index.toNat ≥ fields.length by omega] at run

/-- Failed value-array writes report a source type error. -/
theorem updateArray_error {C F : Type} (args : List ClosSem.Value)
    (s : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : ClosSem.doApp (.memOp .update) args s = .err error) : error = .abort .typeError := by
  simp only [ClosSem.doApp] at run
  cases h : ClosSem.applyMemory .update args s <;> simp [h] at run
  exact run.symm

end Flapjack.Compiler.Backend.ClosToBvl
