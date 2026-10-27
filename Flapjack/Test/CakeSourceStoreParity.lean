import Flapjack.SemanticPrimitivesHOL.Apply

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

-- These cases replay cake_source_apply_probe.out from the pinned HOL source.
private def ffi : Flapjack.HolFfiState Nat :=
  Flapjack.initialHolFfiState (fun _ state _ bytes => .ret state bytes) 42
private def intValue (n : Int) : Value := .litv (.intLit n)

#guard match doAppBasic ([.refv (intValue 5)], ffi) .opref [intValue 7] with
  | some (some (([.refv (.litv (.intLit 5)), .refv (.litv (.intLit 7))], outputFfi),
      .val (.loc true 1))) => outputFfi.ffiState == 42
  | _ => false

#guard match doAppBasic ([.refv (intValue 5)], ffi) .opassign [.loc false 0, intValue 7] with
  | some (some (([.refv (.litv (.intLit 7))], _), .val (.conv none []))) => true
  | _ => false

#guard match doAppBasic ([.refv (intValue 5)], ffi) .opderef [.loc true 1] with
  | some none => true
  | _ => false

#guard match doAppBasic ([.w8array []], ffi) .opassign [.loc true 0, intValue 7] with
  | some none => true
  | _ => false

#guard match doAppBasic ([], ffi) .listAppend [listToValue [intValue 1], listToValue [intValue 2]] with
  | some (some (([], _), .val result)) => match valueToList result with
      | some [.litv (.intLit 1), .litv (.intLit 2)] => true
      | _ => false
  | _ => false

#guard match doAppBasic ([], ffi) (.shift .w8 .lsl 2) [.litv (.word8 7)] with
  | some (some (([], _), .val (.litv (.word8 word)))) => word == 28
  | _ => false

#guard match doAppBasic ([], ffi) .equality [intValue 7, .litv (.word8 7)] with
  | some none => true
  | _ => false

-- Unsupported operations are kept separate from HOL's failed application.
#guard match doAppBasic ([], ffi) .copyStrStr [] with
  | none => true
  | _ => false

-- Safe accesses raise Subscript; unsafe accesses return HOL's NONE.
#guard match doAppBasic ([], ffi) .aw8alloc [intValue 2, .litv (.word8 7)] with
  | some (some (([.w8array [a, b]], _), .val (.loc true 0))) => a == 7 && b == 7
  | _ => false
#guard match doAppBasic ([], ffi) .aw8alloc [intValue (-1), .litv (.word8 7)] with
  | some (some (([], _), .err (.raise (.conv (some (.exnStamp 3)) [])))) => true
  | _ => false
#guard match doAppBasic ([.w8array [4, 7]], ffi) .aw8sub [.loc false 0, intValue 1] with
  | some (some ((_, _), .val (.litv (.word8 b)))) => b == 7
  | _ => false
#guard match doAppBasic ([.w8array [4, 7]], ffi) .aw8sub [.loc true 0, intValue 2] with
  | some (some ((_, _), .err (.raise (.conv (some (.exnStamp 3)) [])))) => true
  | _ => false
#guard match doAppBasic ([.w8array [4, 7]], ffi) .aw8subUnsafe [.loc true 0, intValue 2] with
  | some none => true
  | _ => false
#guard match doAppBasic ([.w8array [4, 7]], ffi) .aw8update [.loc true 0, intValue 1, .litv (.word8 9)] with
  | some (some (([.w8array [a, b]], _), .val (.conv none []))) => a == 4 && b == 9
  | _ => false
#guard match doAppBasic ([], ffi) .aallocFixed [intValue 4, intValue 7] with
  | some (some (([.varray [.litv (.intLit 4), .litv (.intLit 7)]], _), .val (.loc true 0))) => true
  | _ => false
#guard match doAppBasic ([.varray [intValue 4, intValue 7]], ffi) .aupdate
    [.loc false 0, intValue 1, intValue 9] with
  | some (some (([.varray [.litv (.intLit 4), .litv (.intLit 9)]], _), .val (.conv none []))) => true
  | _ => false
#guard match doAppBasic ([.varray [intValue 4]], ffi) .asub [.loc true 0, intValue (-1)] with
  | some (some ((_, _), .err (.raise (.conv (some (.exnStamp 3)) [])))) => true
  | _ => false
#guard match doAppBasic ([], ffi) .vsubUnsafe [.vectorv [intValue 4], intValue (-1)] with
  | some none => true
  | _ => false
#guard match doAppBasic ([.refv (intValue 4)], ffi) .alength [.loc true 0] with
  | some none => true
  | _ => false

end Flapjack.Test.CakeSourceStoreParity
