import Flapjack.SemanticPrimitivesHOL

/-! Store observations captured from the pinned CakeML source semantics. -/
namespace Flapjack.Test.CakeSourceStoreParity
open Flapjack.SemanticPrimitivesHOL

-- The original field types are captured by cake_source_store_probe.out.
example (s : EvalDecsState) : (Nat × Nat) × Value × List Flapjack.AstHOL.Dec →
    Option (Value × List (BitVec 8) × List (BitVec 64)) := s.compiler
example (s : EvalOracleState) : List Value → EvalOracleFun →
    Option ((Nat × Nat) × EvalOracleFun × List Flapjack.AstHOL.Dec) := s.customDoEval
example (s : State Nat) : Flapjack.HolFfiState Nat := s.ffi
example (s : State Nat) : Option EvalState := s.evalState

#guard storeValueSameType (StoreValue.refv 1) (StoreValue.refv 2)
#guard storeValueSameType (StoreValue.thunk .notEvaluated 1) (StoreValue.thunk .evaluated 2)
#guard !storeValueSameType (StoreValue.thunk .evaluated 1) (StoreValue.thunk .notEvaluated 2)
#guard match storeAlloc (StoreValue.refv 7) [StoreValue.refv 3] with
  | ([.refv 3, .refv 7], 1) => true
  | _ => false
#guard match storeLookup 0 [StoreValue.refv 3] with
  | some (.refv 3) => true
  | _ => false
#guard match storeAssign 0 (StoreValue.refv 7) [StoreValue.refv 3] with
  | some [.refv 7] => true
  | _ => false
#guard (storeAssign 1 (StoreValue.refv 7) [StoreValue.refv 3]).isNone
#guard (storeAssign 0 (StoreValue.varray [7]) [StoreValue.refv 3]).isNone

end Flapjack.Test.CakeSourceStoreParity
