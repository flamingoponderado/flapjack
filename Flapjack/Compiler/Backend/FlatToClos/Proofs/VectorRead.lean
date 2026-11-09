import Flapjack.Compiler.Backend.FlatToClos.Proofs.ArrayRead

/-! Vector indexing prerequisites for flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- The emitted checked vector read returns the indexed closure value. -/
theorem evaluate_checkedVectorRead_inBounds {C F : Type} (state : ClosSem.State C F)
    (trace : BackendCommon.Tra) (env : List ClosSem.Value)
    (items : List ClosSem.Value) (index : Int) (value : ClosSem.Value)
    (nonnegative : ¬index < 0) (element : items[index.toNat]? = some value) :
    ClosSem.evaluate
      [.ifThenElse trace
        (.op trace (.blockOp .boundsCheckBlock) [.var trace 0, .var trace 1])
        (.op trace (.memOp .el) [.var trace 0, .var trace 1])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))]
      (.number index :: .block 0 items :: env) state = (.val [value], state) := by
  have bound : index.toNat < items.length := (List.getElem?_eq_some_iff.mp element).1
  have valueEq : items[index.toNat] = value := (List.getElem?_eq_some_iff.mp element).2
  have valid : 0 ≤ index ∧ index < (items.length : Int) := by omega
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyMemory, ClosSem.applyBlock,
    ClosSem.boolValue, ClosSem.asBool, BackendCommon.trueTag, valid, nonnegative, valueEq]

/-- The emitted checked vector read raises Subscript outside bounds. -/
theorem evaluate_checkedVectorRead_outOfBounds {C F : Type} (state : ClosSem.State C F)
    (trace : BackendCommon.Tra) (env : List ClosSem.Value) (items : List ClosSem.Value) (index : Int)
    (bad : index < 0 ∨ items.length ≤ index.toNat) :
    ClosSem.evaluate
      [.ifThenElse trace
        (.op trace (.blockOp .boundsCheckBlock) [.var trace 0, .var trace 1])
        (.op trace (.memOp .el) [.var trace 0, .var trace 1])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))]
      (.number index :: .block 0 items :: env) state = (.err (.raise (.block 3 [])), state) := by
  have invalid : ¬(0 ≤ index ∧ index < (items.length : Int)) := by omega
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock,
    ClosSem.boolValue, ClosSem.asBool, BackendCommon.falseTag, invalid]

/-- The emitted checked string read returns the selected byte as a number. -/
theorem evaluate_checkedStringRead_inBounds {C F : Type} (state : ClosSem.State C F)
    (trace : BackendCommon.Tra) (env : List ClosSem.Value)
    (bytes : List (BitVec 8)) (index : Int) (byte : BitVec 8)
    (nonnegative : ¬index < 0) (element : bytes[index.toNat]? = some byte) :
    ClosSem.evaluate
      [.ifThenElse trace
        (.op trace (.memOp (.boundsCheckByte false)) [.var trace 0, .var trace 1])
        (.op trace (.memOp .derefByteVec) [.var trace 0, .var trace 1])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))]
      (.number index :: .byteVector bytes :: env) state = (.val [.number byte.toNat], state) := by
  have bound : index.toNat < bytes.length := (List.getElem?_eq_some_iff.mp element).1
  have byteEq : bytes[index.toNat] = byte := (List.getElem?_eq_some_iff.mp element).2
  have valid : 0 ≤ index ∧ index < (bytes.length : Int) := by omega
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyMemory,
    ClosSem.boolValue, ClosSem.asBool, BackendCommon.trueTag, valid, nonnegative, byteEq]

/-- The emitted checked string read raises Subscript outside bounds. -/
theorem evaluate_checkedStringRead_outOfBounds {C F : Type} (state : ClosSem.State C F)
    (trace : BackendCommon.Tra) (env : List ClosSem.Value) (bytes : List (BitVec 8)) (index : Int)
    (bad : index < 0 ∨ bytes.length ≤ index.toNat) :
    ClosSem.evaluate
      [.ifThenElse trace
        (.op trace (.memOp (.boundsCheckByte false)) [.var trace 0, .var trace 1])
        (.op trace (.memOp .derefByteVec) [.var trace 0, .var trace 1])
        (.raise trace (.op trace (.blockOp (.cons 3)) []))]
      (.number index :: .byteVector bytes :: env) state = (.err (.raise (.block 3 [])), state) := by
  have invalid : ¬(0 ≤ index ∧ index < (bytes.length : Int)) := by omega
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyMemory, ClosSem.applyBlock,
    ClosSem.boolValue, ClosSem.asBool, BackendCommon.falseTag, invalid]

/-- Exploding bytes yields lists of related characters and closure numbers. -/
theorem explodedChars_related (bytes : List (BitVec 8)) :
    List.Forall₂ ValueRel (bytes.map (FlatSem.Value.litv ∘ Flapjack.AstHOL.Lit.char))
      (bytes.map (fun byte => ClosSem.Value.number byte.toNat)) := by
  induction bytes with
  | nil => exact .nil
  | cons byte rest ih => exact .cons (.char byte) ih


end Flapjack.Compiler.Backend.FlatToClos
