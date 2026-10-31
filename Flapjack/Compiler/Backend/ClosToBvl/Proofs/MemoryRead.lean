import Flapjack.Compiler.Backend.ClosToBvl.Proofs.IntegerRelation
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateBlockCons

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

/-- Looking up a related field preserves its value relation. -/
theorem relatedFields_lookup {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {source : List ClosSem.Value} {target : List BvlSem.Value}
    (related : List.Forall₂ (vRel maxApp f refs code) source target)
    (index : Nat) (value : ClosSem.Value) (found : source[index]? = some value) :
    ∃ targetValue, target[index]? = some targetValue ∧ vRel maxApp f refs code value targetValue := by
  induction related generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst value
      exact ⟨_, rfl, head⟩
    | succ index =>
      simp only [List.getElem?_cons_succ] at found ⊢
      exact ih index found

/-- Indexed access on related blocks has the same result relation. -/
theorem memoryEl_block {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (s : ClosSem.State C F) (t : BvlSem.State C F)
    (tag : Nat) (fields : List ClosSem.Value) (target : BvlSem.Value)
    (blockRel : vRel s.maxApp f t.refs t.code (.block tag fields) target)
    (index : Int) (nonnegative : ¬ index < 0) (value : ClosSem.Value)
    (found : fields[index.toNat]? = some value) :
    ∃ result, BvlSem.doApp (.memOp .el) [target, .number index] t = .val (result, t) ∧
      vRel s.maxApp f t.refs t.code value result := by
  obtain ⟨targetFields, rfl, fieldsRel⟩ := vRel_block_inv blockRel
  obtain ⟨result, targetFound, resultRel⟩ := relatedFields_lookup fieldsRel index.toNat value found
  exact ⟨result, by simp [BvlSem.doApp, BvlSem.applyMemory, nonnegative, targetFound], resultRel⟩

/-- Indexed access on related mutable arrays has the same result relation. -/
theorem memoryEl_array {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (states : stateRel f s t)
    (flag : Bool) (ptr targetPtr : Nat) (mapped : f.lookup ptr = some targetPtr)
    (fields : List ClosSem.Value) (arrayFound : s.refs.lookup ptr = some (.valueArray fields))
    (index : Int) (nonnegative : ¬ index < 0) (value : ClosSem.Value)
    (found : fields[index.toNat]? = some value) :
    ∃ result, BvlSem.doApp (.memOp .el) [.refPtr flag targetPtr, .number index] t = .val (result, t) ∧
      vRel s.maxApp f t.refs t.code value result := by
  obtain ⟨targetFields, targetArray, fieldsRel⟩ := stateRel_array_lookup states ptr targetPtr fields mapped arrayFound
  obtain ⟨result, targetFound, resultRel⟩ := relatedFields_lookup fieldsRel index.toNat value found
  exact ⟨result, by simp [BvlSem.doApp, BvlSem.applyMemory, targetArray, nonnegative, targetFound], resultRel⟩

/-- Successful indexed block or mutable-array access preserves related values. -/
theorem memoryEl_dispatch {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (args : List ClosSem.Value) (targets : List BvlSem.Value)
    (s next : ClosSem.State C F) (t : BvlSem.State C F) (states : stateRel f s t)
    (related : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targets)
    (value : ClosSem.Value) (run : ClosSem.doApp (.memOp .el) args s = .val (value, next)) :
    ∃ target, BvlSem.doApp (.memOp .el) targets t = .val (target, t) ∧
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
        case block.number tag fields index =>
          cases related with
          | cons firstRel tail =>
            cases tail with
            | cons secondRel tail =>
              cases tail
              have secondEq := vRel_number_inv secondRel
              subst_vars
              by_cases negative : index < 0
              · simp [negative] at run
              · cases found : fields[index.toNat]? with
                | none => simp [negative, found] at run
                | some field =>
                  simp [negative, found] at run
                  rcases run with ⟨rfl, rfl⟩
                  obtain ⟨target, targetRun, valueRel⟩ := memoryEl_block s t tag fields _ firstRel index negative field found
                  exact ⟨target, targetRun, rfl, valueRel⟩
        case refPtr.number flag ptr index =>
          cases related with
          | cons firstRel tail =>
            cases tail with
            | cons secondRel tail =>
              cases tail
              obtain ⟨targetPtr, rfl, mapped⟩ := vRel_refPtr_inv firstRel
              have secondEq := vRel_number_inv secondRel
              subst_vars
              cases arrayFound : s.refs.lookup ptr with
              | none => simp [arrayFound] at run
              | some cell =>
                cases cell with
                | byteArray bytes => simp [arrayFound] at run
                | thunk mode value => simp [arrayFound] at run
                | valueArray fields =>
                  by_cases negative : index < 0
                  · simp [arrayFound, negative] at run
                  · cases found : fields[index.toNat]? with
                    | none => simp [arrayFound, negative, found] at run
                    | some field =>
                      simp [arrayFound, negative, found] at run
                      rcases run with ⟨rfl, rfl⟩
                      obtain ⟨target, targetRun, valueRel⟩ :=
                        memoryEl_array s t states flag ptr targetPtr mapped fields arrayFound index negative field found
                      exact ⟨target, targetRun, rfl, valueRel⟩

/-- A failed indexed access reports a source type error. -/
theorem memoryEl_error {C F : Type} (args : List ClosSem.Value)
    (s : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : ClosSem.doApp (.memOp .el) args s = .err error) : error = .abort .typeError := by
  simp only [ClosSem.doApp] at run
  cases h : ClosSem.applyMemory .el args s <;> simp [h] at run
  exact run.symm

/-- Array bounds checks agree for related mutable arrays. -/
theorem memoryBoundsArray_dispatch {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (args : List ClosSem.Value) (targets : List BvlSem.Value)
    (s next : ClosSem.State C F) (t : BvlSem.State C F) (states : stateRel f s t)
    (related : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targets)
    (value : ClosSem.Value) (run : ClosSem.doApp (.memOp .boundsCheckArray) args s = .val (value, next)) :
    ∃ target, BvlSem.doApp (.memOp .boundsCheckArray) targets t = .val (target, t) ∧
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
                | byteArray bytes => simp [found] at run
                | thunk mode value => simp [found] at run
                | valueArray fields =>
                  simp [found] at run
                  rcases run with ⟨rfl, rfl⟩
                  obtain ⟨targetFields, targetFound, fieldsRel⟩ :=
                    stateRel_array_lookup states ptr targetPtr fields mapped found
                  let bound := decide (0 ≤ index ∧ index < Int.ofNat fields.length)
                  refine ⟨BvlSem.boolValue bound, ?_, rfl, ?_⟩
                  · simp [BvlSem.doApp, BvlSem.applyMemory, targetFound, fieldsRel.length_eq, bound]
                  · simpa [bound] using (vRel_bool (maxApp := s.maxApp) (f := f) (refs := t.refs) (code := t.code) bound)

/-- Failed mutable-array bounds checks report a source type error. -/
theorem memoryBoundsArray_error {C F : Type} (args : List ClosSem.Value)
    (s : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : ClosSem.doApp (.memOp .boundsCheckArray) args s = .err error) : error = .abort .typeError := by
  simp only [ClosSem.doApp] at run
  cases h : ClosSem.applyMemory .boundsCheckArray args s <;> simp [h] at run
  exact run.symm

end Flapjack.Compiler.Backend.ClosToBvl
