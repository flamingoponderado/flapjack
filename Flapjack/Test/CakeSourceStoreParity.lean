import Flapjack.SemanticPrimitivesHOL.ApplyNumeric

/-! Store observations captured from the pinned CakeML source semantics. -/
namespace Flapjack.Test.CakeSourceStoreParity
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

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
#guard match doAppBasic ([], ffi) (.arith .add .intT) [] with
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

private def stringValue (s : String) : Value := .litv (.strLit (ofString s))

#guard match doAppBasic ([], ffi) .copyStrStr [stringValue "abcd", intValue 1, intValue 2] with
  | some (some (([], _), .val (.litv (.strLit str)))) => str == ofString "bc"
  | _ => false
#guard match doAppBasic ([], ffi) .copyStrStr [stringValue "abcd", intValue 3, intValue 2] with
  | some (some (([], _), .err (.raise (.conv (some (.exnStamp 3)) [])))) => true
  | _ => false
#guard match doAppBasic ([.w8array [1, 2, 3, 4]], ffi) .copyAw8Aw8
    [.loc true 0, intValue 0, intValue 3, .loc false 0, intValue 1] with
  | some (some (([.w8array [a, b, c, d]], _), .val (.conv none []))) =>
      a == 1 && b == 1 && c == 2 && d == 3
  | _ => false
#guard match doAppBasic ([.w8array [0, 0, 0]], ffi) .copyStrAw8
    [stringValue "abc", intValue 1, intValue 2, .loc true 0, intValue 1] with
  | some (some (([.w8array [a, b, c]], _), .val (.conv none []))) => a == 0 && b == 98 && c == 99
  | _ => false
#guard match doAppBasic ([.w8array [1, 2, 3]], ffi) .xorAw8StrUnsafe [.loc false 0, stringValue "AB"] with
  | some (some (([.w8array [a, b, c]], _), .val (.conv none []))) => a == 64 && b == 64 && c == 3
  | _ => false
#guard match doAppBasic ([.w8array [1]], ffi) .xorAw8StrUnsafe [.loc true 0, stringValue "AB"] with
  | some none => true
  | _ => false
#guard match doAppBasic ([], ffi) .strsub [stringValue "abc", intValue (-1)] with
  | some (some (([], _), .err (.raise (.conv (some (.exnStamp 3)) [])))) => true
  | _ => false
#guard match doAppBasic ([], ffi) .envId [.conv none [intValue 5, intValue 9]] with
  | some (some (([], _), .val (.conv none [.litv (.intLit 5), .litv (.intLit 9)]))) => true
  | _ => false
#guard match doAppBasic ([.w8array [1, 2]], ffi) (.ffi (ofString "")) [stringValue "x", .loc true 0] with
  | some (some (([.w8array [a, b]], outFfi), .val (.conv none []))) => a == 1 && b == 2 && outFfi.ffiState == 42
  | _ => false
#guard match doAppBasic ([], ffi) (.thunkOp (.allocThunk .notEvaluated)) [intValue 5] with
  | some (some (([.thunk .notEvaluated (.litv (.intLit 5))], _), .val (.loc false 0))) => true
  | _ => false

private def failingFfi : Flapjack.HolFfiState Nat :=
  Flapjack.initialHolFfiState (fun _ _ _ _ => .final .failed) 41
#guard match doAppBasic ([.w8array [1]], failingFfi) (.ffi (ofString "test")) [stringValue "x", .loc true 0] with
  | some (some (([.w8array [a]], outFfi), .err (.abort (.ffiError event)))) =>
      a == 1 && outFfi.ffiState == 41 && outFfi.ioEvents.isEmpty && event.configuration == [120] && event.bytes == [1]
  | _ => false

private def returningFfi : Flapjack.HolFfiState Nat :=
  Flapjack.initialHolFfiState (fun _ state _ _ => .ret (state + 1) [9]) 41
#guard match doAppBasic ([.w8array [1]], returningFfi) (.ffi (ofString "test")) [stringValue "x", .loc true 0] with
  | some (some (([.w8array [a]], outFfi), .val (.conv none []))) =>
      a == 9 && outFfi.ffiState == 42 &&
        match outFfi.ioEvents with
        | [event] => event.configuration == [120] && event.bytes == [(1, 9)]
        | _ => false
  | _ => false

-- Integer division and modulus use HOL's flooring convention, including a
-- negative divisor; Lean's default Euclidean division differs in that case.
#guard match doAppNumericCore ([], ffi) (.arith .div .intT) [intValue (-7), intValue 3] with
  | some (some (([], _), .val (.litv (.intLit (-3))))) => true
  | _ => false
#guard match doAppNumericCore ([], ffi) (.arith .div .intT) [intValue 7, intValue (-3)] with
  | some (some (([], _), .val (.litv (.intLit (-3))))) => true
  | _ => false
#guard match doAppNumericCore ([], ffi) (.arith .mod .intT) [intValue 7, intValue (-3)] with
  | some (some (([], _), .val (.litv (.intLit (-2))))) => true
  | _ => false
#guard match doAppNumericCore ([], ffi) (.arith .div .intT) [intValue 7, intValue 0] with
  | some (some (([], _), .err (.raise (.conv (some (.exnStamp 2)) [])))) => true
  | _ => false
#guard match doAppNumericCore ([], ffi) (.fromTo .intT (.wordT .w8)) [intValue (-1)] with
  | some (some (([], _), .val (.litv (.word8 w)))) => w == 255
  | _ => false
#guard match doAppNumericCore ([], ffi) (.fromTo .intT .charT) [intValue 256] with
  | some (some (([], _), .err (.raise (.conv (some (.exnStamp 1)) [])))) => true
  | _ => false
#guard match doAppNumericCore ([], ffi) (.arith .add (.wordT .w8)) [.litv (.word8 255), .litv (.word8 2)] with
  | some (some (([], _), .val (.litv (.word8 w)))) => w == 1
  | _ => false
#guard match doAppNumericCore ([], ffi) (.arith .not .boolT) [boolValue true] with
  | some (some (([], _), .val (.conv (some (.typeStamp name 0)) []))) => name == ofString "False"
  | _ => false
#guard match doAppNumericCore ([], ffi) (.arith .add .intT) [.litv (.word8 1), intValue 2] with
  | some none => true
  | _ => false

-- Check that the assembled noncomputable dispatcher selects the same actual
-- arithmetic and reference branches; noncomputability comes from float cases.
example : doApp ([], ffi) (.arith .div .intT) [intValue 7, intValue (-3)] =
    some (([], ffi), .val (intValue (-3))) := by rfl
example : doApp ([], ffi) .opref [intValue 7] =
    some (([.refv (intValue 7)], ffi), .val (.loc true 0)) := by rfl
example : doApp ([], ffi) .opapp [] = none := by rfl

private def noVars : Flapjack.AstHOL.Exp → Bool
  | .var _ => false
  | _ => true

-- Nested expressions, pattern branches, and recursive function bodies are
-- all visited by the original ast$every_exp (see the pinned HOL probe).
#guard !Flapjack.AstHOL.everyExp noVars
  (.if_ (.lit (.intLit 1)) (.con none [.lit (.intLit 2), .var (.short (ofString "x"))]) (.lit (.intLit 3)))
#guard !Flapjack.AstHOL.everyExp noVars
  (.mat (.lit (.intLit 0)) [(.pany, .lit (.intLit 1)), (.pany, .var (.short (ofString "x")))])
#guard !Flapjack.AstHOL.everyExp noVars
  (.letrec [(ofString "f", ofString "x", .var (.short (ofString "x")))] (.lit (.intLit 0)))
#guard Flapjack.AstHOL.everyExp noVars
  (.letrec [(ofString "f", ofString "x", .lit (.intLit 1))] (.lit (.intLit 0)))

-- The FMA argument order follows fp64_mul_add y z x in the HOL source.
example (x y z : BitVec 64) :
    doApp ([], ffi) (.arith .fma .float64T)
      [.litv (.float64 x), .litv (.float64 y), .litv (.float64 z)] =
    some (([], ffi), .val (.litv (.float64 (Flapjack.fpSemFpfma x y z)))) := by rfl

end Flapjack.Test.CakeSourceStoreParity
