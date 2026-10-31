import Flapjack.Compiler.Backend.ClosToBvl.Proofs.IntegerRelation

/-! Mutable reference lookup for the closure-to-BVL simulation candidate. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL

/-- A source reference pointer is related only to the corresponding relocated
pointer with the same mutability flag. -/
theorem vRel_refPtr_inv {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {flag : Bool} {pointer : Nat} {target : BvlSem.Value}
    (related : vRel maxApp f refs code (.refPtr flag pointer) target) :
    ∃ targetPointer, target = .refPtr flag targetPointer ∧ f.lookup pointer = some targetPointer := by
  cases related with
  | refPtr found => exact ⟨_, rfl, found⟩
  | closure _ closure => cases closure
  | partialClosure _ _ _ _ _ added _ closure => cases closure <;> simp [addArgs] at added

/-- The state relation relates the cells at any relocated source reference. -/
theorem stateRel_ref_lookup {C F : Type} {f : HolFiniteMapExact Nat Nat}
    {s : ClosSem.State C F} {t : BvlSem.State C F} (states : stateRel f s t)
    (sourcePtr targetPtr : Nat) (cell : ClosSem.Ref ClosSem.Value)
    (mapped : f.lookup sourcePtr = some targetPtr) (found : s.refs.lookup sourcePtr = some cell) :
    ∃ targetCell, t.refs.lookup targetPtr = some targetCell ∧
      refRel (vRel s.maxApp f t.refs t.code) cell targetCell := by
  obtain ⟨_, _, _, _, _, _, _, cells, _⟩ := states
  obtain ⟨targetCell, ptr, mapFound, targetFound, related⟩ := cells sourcePtr cell found
  have ptrEq : ptr = targetPtr := Option.some.inj (mapFound.symm.trans mapped)
  subst ptr
  exact ⟨targetCell, targetFound, related⟩

/-- Reading a relocated array preserves its pointwise value relation. -/
theorem stateRel_array_lookup {C F : Type} {f : HolFiniteMapExact Nat Nat}
    {s : ClosSem.State C F} {t : BvlSem.State C F} (states : stateRel f s t)
    (sourcePtr targetPtr : Nat) (values : List ClosSem.Value)
    (mapped : f.lookup sourcePtr = some targetPtr)
    (found : s.refs.lookup sourcePtr = some (.valueArray values)) :
    ∃ targetValues, t.refs.lookup targetPtr = some (.valueArray targetValues) ∧
      List.Forall₂ (vRel s.maxApp f t.refs t.code) values targetValues := by
  obtain ⟨target, targetFound, related⟩ := stateRel_ref_lookup states sourcePtr targetPtr _ mapped found
  cases target <;> simp [refRel] at related
  exact ⟨_, targetFound, related⟩

/-- Reading a relocated mutable byte array preserves its contents and its
unfrozen target representation. -/
theorem stateRel_bytes_lookup {C F : Type} {f : HolFiniteMapExact Nat Nat}
    {s : ClosSem.State C F} {t : BvlSem.State C F} (states : stateRel f s t)
    (sourcePtr targetPtr : Nat) (bytes : List (BitVec 8))
    (mapped : f.lookup sourcePtr = some targetPtr)
    (found : s.refs.lookup sourcePtr = some (.byteArray bytes)) :
    t.refs.lookup targetPtr = some (.byteArray false bytes) := by
  obtain ⟨target, targetFound, related⟩ := stateRel_ref_lookup states sourcePtr targetPtr _ mapped found
  cases target <;> simp [refRel] at related
  obtain ⟨rfl, rfl⟩ := related
  exact targetFound

/-- Mutable array length operations. -/
inductive MemoryLength where
  | array
  | bytes

def MemoryLength.op : MemoryLength → ClosLang.MemOp
  | .array => .length
  | .bytes => .lengthByte

/-- Successful mutable array length checks return the same integer on both
sides, without changing either state. -/
theorem memoryLength_dispatch {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (op : MemoryLength) (args : List ClosSem.Value) (targets : List BvlSem.Value)
    (s next : ClosSem.State C F) (t : BvlSem.State C F) (states : stateRel f s t)
    (related : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targets)
    (value : ClosSem.Value) (run : ClosSem.doApp (.memOp op.op) args s = .val (value, next)) :
    ∃ target, BvlSem.doApp (.memOp op.op) targets t = .val (target, t) ∧
      next = s ∧ vRel s.maxApp f t.refs t.code value target := by
  cases args with
  | nil => cases op <;> simp [MemoryLength.op, ClosSem.doApp, ClosSem.applyMemory] at run
  | cons first rest =>
    cases rest with
    | cons second rest => cases op <;> simp [MemoryLength.op, ClosSem.doApp, ClosSem.applyMemory] at run
    | nil =>
      cases first <;> cases op <;> simp only [MemoryLength.op, ClosSem.doApp, ClosSem.applyMemory] at run
      all_goals try contradiction
      case refPtr.array flag ptr =>
        cases related with
        | cons head tail =>
          cases tail
          obtain ⟨targetPtr, rfl, mapped⟩ := vRel_refPtr_inv head
          cases found : s.refs.lookup ptr with
          | none => simp [found] at run
          | some cell =>
            cases cell with
            | valueArray values =>
              simp [found] at run
              rcases run with ⟨rfl, rfl⟩
              obtain ⟨targets, targetFound, fields⟩ := stateRel_array_lookup states ptr targetPtr values mapped found
              refine ⟨.number targets.length, ?_, rfl, ?_⟩
              · simp [MemoryLength.op, BvlSem.doApp, BvlSem.applyMemory, targetFound]
              · simpa [fields.length_eq] using (vRel.number (Int.ofNat values.length))
            | byteArray bytes => simp [found] at run
            | thunk mode value => simp [found] at run
      case refPtr.bytes flag ptr =>
        cases related with
        | cons head tail =>
          cases tail
          obtain ⟨targetPtr, rfl, mapped⟩ := vRel_refPtr_inv head
          cases found : s.refs.lookup ptr with
          | none => simp [found] at run
          | some cell =>
            cases cell with
            | valueArray values => simp [found] at run
            | byteArray bytes =>
              simp [found] at run
              rcases run with ⟨rfl, rfl⟩
              have targetFound := stateRel_bytes_lookup states ptr targetPtr bytes mapped found
              exact ⟨.number bytes.length, by simp [MemoryLength.op, BvlSem.doApp, BvlSem.applyMemory, targetFound],
                rfl, .number _⟩
            | thunk mode value => simp [found] at run

/-- A failed mutable-array length operation reports a type error. -/
theorem memoryLength_error {C F : Type} (op : MemoryLength) (args : List ClosSem.Value)
    (s : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : ClosSem.doApp (.memOp op.op) args s = .err error) : error = .abort .typeError := by
  simp only [ClosSem.doApp] at run
  cases h : ClosSem.applyMemory op.op args s <;> simp [h] at run
  exact run.symm

/-- A successful mutable-byte read returns the same numeric byte on both
sides of the relation. -/
theorem memoryByte_read {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (states : stateRel f s t)
    (sourcePtr targetPtr : Nat) (flag : Bool) (bytes : List (BitVec 8)) (index : Int) (byte : BitVec 8)
    (mapped : f.lookup sourcePtr = some targetPtr)
    (found : s.refs.lookup sourcePtr = some (.byteArray bytes))
    (nonnegative : ¬ index < 0) (inBounds : bytes[index.toNat]? = some byte) :
    ClosSem.doApp (.memOp .derefByte) [.refPtr flag sourcePtr, .number index] s =
      .val (.number byte.toNat, s) ∧
    BvlSem.doApp (.memOp .derefByte) [.refPtr flag targetPtr, .number index] t =
      .val (.number byte.toNat, t) ∧
    vRel s.maxApp f t.refs t.code (.number byte.toNat) (.number byte.toNat) := by
  have targetFound := stateRel_bytes_lookup states sourcePtr targetPtr bytes mapped found
  refine ⟨?_, ?_, .number _⟩
  · simp [ClosSem.doApp, ClosSem.applyMemory, found, nonnegative, inBounds]
  · simp [BvlSem.doApp, BvlSem.applyMemory, targetFound, nonnegative, inBounds]

/-- Successful byte dereference on related arguments produces related values. -/
theorem memoryByte_dispatch {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (args : List ClosSem.Value) (targets : List BvlSem.Value)
    (s next : ClosSem.State C F) (t : BvlSem.State C F) (states : stateRel f s t)
    (related : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targets)
    (value : ClosSem.Value) (run : ClosSem.doApp (.memOp .derefByte) args s = .val (value, next)) :
    ∃ target, BvlSem.doApp (.memOp .derefByte) targets t = .val (target, t) ∧
      next = s ∧ vRel s.maxApp f t.refs t.code value target := by
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
        case refPtr.number flag ptr index =>
          cases related with
          | cons firstRel tail =>
            cases tail with
            | cons secondRel tail =>
              cases tail
              obtain ⟨targetPtr, rfl, mapped⟩ := vRel_refPtr_inv firstRel
              have secondEq := vRel_number_inv secondRel
              subst_vars
              cases found : s.refs.lookup ptr with
              | none => simp [found] at run
              | some cell =>
                cases cell with
                | valueArray values => simp [found] at run
                | thunk mode value => simp [found] at run
                | byteArray bytes =>
                  by_cases negative : index < 0
                  · simp [found, negative] at run
                  · cases byteFound : bytes[index.toNat]? with
                    | none => simp [found, negative, byteFound] at run
                    | some byte =>
                      simp [found, negative, byteFound] at run
                      rcases run with ⟨rfl, rfl⟩
                      have reads := memoryByte_read s t states ptr targetPtr flag bytes index byte mapped found negative byteFound
                      exact ⟨.number byte.toNat, reads.2.1, rfl, reads.2.2⟩

/-- A failed byte dereference reports a type error. -/
theorem memoryByte_error {C F : Type} (args : List ClosSem.Value)
    (s : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : ClosSem.doApp (.memOp .derefByte) args s = .err error) : error = .abort .typeError := by
  simp only [ClosSem.doApp] at run
  cases h : ClosSem.applyMemory .derefByte args s <;> simp [h] at run
  exact run.symm

end Flapjack.Compiler.Backend.ClosToBvl
