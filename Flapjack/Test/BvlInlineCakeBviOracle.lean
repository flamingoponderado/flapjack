-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Compiler.Backend.Bvi.Syntax

namespace Flapjack.Test.BvlInlineCakeBviOracle

private def matches0 (entry : Nat × Nat × Flapjack.Compiler.Backend.Bvi.Exp) : Bool :=
  match entry with
  | (62, 1, (.let [(.op ((.globOp .globalsPtr)) [])] ((.let [(.op ((.memOp .el)) [(.op ((.intOp ((.const 0)))) []), (.var 0)])] ((.let [(.op ((.intOp .add)) [(.var 0), (.var 2)])] ((.let [(.op ((.memOp .length)) [(.var 2)])] ((.let [(.op ((.memOp .update)) [(.var 1), (.op ((.intOp ((.const 0)))) []), (.var 3)])] ((.ifThenElse ((.op ((.intOp .less)) [(.var 1), (.var 2)])) ((.var 0)) ((.let [(.op ((.memOp .refArray)) [(.op ((.intOp ((.const 0)))) []), (.op ((.intOp .add)) [(.var 2), (.var 2)])])] ((.let [(.op ((.globOp .setGlobalsPtr)) [(.var 0)])] ((.call 0 ((some 63)) [(.var 1), (.var 6), (.op ((.intOp .sub)) [(.op ((.intOp ((.const 1)))) []), (.var 3)])] none)))))))))))))))))) => true
  | _ => false

private def matches1 (entry : Nat × Nat × Flapjack.Compiler.Backend.Bvi.Exp) : Bool :=
  match entry with
  | (63, 3, (.let [(.op ((.memOp .update)) [(.op ((.memOp .el)) [(.var 2), (.var 1)]), (.var 2), (.var 0)])] ((.ifThenElse ((.op ((.blockOp .equal)) [(.op ((.intOp ((.const 0)))) []), (.var 3)])) ((.var 0)) ((.call 0 ((some 63)) [(.var 1), (.var 2), (.op ((.intOp .sub)) [(.op ((.intOp ((.const 1)))) []), (.var 3)])] none)))))) => true
  | _ => false

private def matches2 (entry : Nat × Nat × Flapjack.Compiler.Backend.Bvi.Exp) : Bool :=
  match entry with
  | (64, 0, (.let [(.op ((.memOp .refArray)) [(.op ((.intOp ((.const 0)))) []), (.op ((.intOp ((.const 3)))) [])])] ((.let [(.op ((.memOp .update)) [(.op ((.intOp ((.const 1)))) []), (.op ((.intOp ((.const 0)))) []), (.var 0)])] ((.let [(.op ((.globOp .setGlobalsPtr)) [(.var 1)])] ((.call 0 ((some 88)) [] ((some ((.var 0)))))))))))) => true
  | _ => false

private def matches3 (entry : Nat × Nat × Flapjack.Compiler.Backend.Bvi.Exp) : Bool :=
  match entry with
  | (65, 2, (.ifThenElse ((.op ((.blockOp ((.tagLenEq 0 0)))) [(.var 0)])) ((.var 1)) ((.call 0 ((some 65)) [(.op ((.memOp .el)) [(.op ((.intOp ((.const 1)))) []), (.var 0)]), (.op ((.intOp .add)) [(.var 1), (.op ((.intOp ((.const 1)))) [])])] none)))) => true
  | _ => false

private def matches4 (entry : Nat × Nat × Flapjack.Compiler.Backend.Bvi.Exp) : Bool :=
  match entry with
  | (66, 3, (.ifThenElse ((.op ((.blockOp ((.tagLenEq 0 0)))) [(.var 0)])) ((.var 2)) ((.let [(.op ((.memOp .updateByte)) [(.op ((.memOp .el)) [(.op ((.intOp ((.const 0)))) []), (.var 0)]), (.var 1), (.var 2)])] ((.call 0 ((some 66)) [(.op ((.memOp .el)) [(.op ((.intOp ((.const 1)))) []), (.var 1)]), (.op ((.intOp .add)) [(.var 2), (.op ((.intOp ((.const 1)))) [])]), (.var 3)] none)))))) => true
  | _ => false

private def matches5 (entry : Nat × Nat × Flapjack.Compiler.Backend.Bvi.Exp) : Bool :=
  match entry with
  | (67, 3, (.ifThenElse ((.op ((.blockOp ((.equalConst ((.int 0)))))) [(.var 1)])) ((.var 0)) ((.let [(.op ((.intOp .sub)) [(.op ((.intOp ((.const 1)))) []), (.var 1)])] ((.let [(.op ((.memOp .derefByte)) [(.var 0), (.var 3)])] ((.call 0 ((some 67)) [(.op ((.blockOp ((.cons 0)))) [(.var 2), (.var 0)]), (.var 1), (.var 4)] none)))))))) => true
  | _ => false

private def matches6 (entry : Nat × Nat × Flapjack.Compiler.Backend.Bvi.Exp) : Bool :=
  match entry with
  | (68, 2, (.ifThenElse ((.op ((.blockOp ((.tagLenEq 0 0)))) [(.var 0)])) ((.var 1)) ((.call 0 ((some 68)) [(.op ((.memOp .el)) [(.op ((.intOp ((.const 1)))) []), (.var 0)]), (.op ((.intOp .add)) [(.var 1), (.op ((.memOp .lengthByte)) [(.op ((.memOp .el)) [(.op ((.intOp ((.const 0)))) []), (.var 0)])])])] none)))) => true
  | _ => false

private def matches7 (entry : Nat × Nat × Flapjack.Compiler.Backend.Bvi.Exp) : Bool :=
  match entry with
  | (69, 3, (.ifThenElse ((.op ((.blockOp ((.tagLenEq 0 0)))) [(.var 0)])) ((.var 2)) ((.let [(.op ((.memOp .el)) [(.op ((.intOp ((.const 0)))) []), (.var 0)])] ((.let [(.op ((.memOp .lengthByte)) [(.var 0)])] ((.let [(.op ((.memOp ((.copyByte false)))) [(.var 3), (.var 4), (.var 0), (.op ((.intOp ((.const 0)))) []), (.var 1)])] ((.call 0 ((some 69)) [(.op ((.memOp .el)) [(.op ((.intOp ((.const 1)))) []), (.var 3)]), (.op ((.intOp .add)) [(.var 4), (.var 1)]), (.var 5)] none)))))))))) => true
  | _ => false

private def matches8 (entry : Nat × Nat × Flapjack.Compiler.Backend.Bvi.Exp) : Bool :=
  match entry with
  | (72, 2, (.let [(.op ((.intOp .sub)) [(.op ((.intOp ((.const 1)))) []), (.op (.blockOp (.elemAt 1)) [((.var 1))])])] ((.ifThenElse ((.op ((.intOp .less)) [(.op ((.intOp ((.const 0)))) []), (.var 0)])) ((.let [(.op (.blockOp (.elemAt 1)) [((.var 2))])] ((.ifThenElse ((.op ((.intOp ((.lessConstSmall 1)))) [(.var 0)])) ((.let [(.call 0 none [(.var 2), (.var 3), (.op (.blockOp (.elemAt 0)) [((.var 3))])] none)] ((.ifThenElse ((.op ((.blockOp ((.equalConst ((.int 0)))))) [(.op (.blockOp (.elemAt 1)) [((.var 0))])])) ((.call 0 none [(.var 0), (.op (.blockOp (.elemAt 0)) [((.var 0))])] none)) ((.call 0 ((some 72)) [(.var 0)] none)))))) ((.let [(.call 0 none [(.var 1), (.var 2), (.var 3), (.op (.blockOp (.elemAt 0)) [((.var 3))])] none)] ((.ifThenElse ((.op ((.blockOp ((.equalConst ((.int 0)))))) [(.op (.blockOp (.elemAt 1)) [((.var 0))])])) ((.call 0 none [(.var 0), (.op (.blockOp (.elemAt 0)) [((.var 0))])] none)) ((.call 0 ((some 72)) [(.var 0)] none)))))))))) ((.ifThenElse ((.op ((.blockOp ((.tagEq 30)))) [(.var 2)])) ((.op ((.blockOp ((.cons 31)))) [(.var 1), (.var 2), (.var 0), (.op ((.memOp .el)) [(.let [(.op (.blockOp (.elemAt 1)) [((.var 2))])] ((.op ((.intOp .add)) [(.op ((.intOp ((.const 0)))) []), (.op ((.intOp .div)) [(.op ((.intOp ((.const 2)))) []), (.op ((.intOp .mult)) [(.var 0), (.op ((.intOp .sub)) [(.op ((.intOp ((.const 1)))) []), (.var 0)])])])]))), (.op ((.globOp ((.global 1)))) [])])])) ((.let [(.op ((.intOp .sub)) [(.op ((.intOp ((.const 3)))) []), (.op ((.blockOp .lengthBlock)) [(.var 2)])])] ((.op ((.blockOp ((.consExtend 31)))) [(.var 2), (.op (.blockOp (.elemAt 2)) [((.var 3))]), (.var 1), (.op ((.memOp .el)) [(.let [(.op ((.intOp .add)) [(.var 0), (.op ((.intOp .add)) [(.op ((.intOp ((.const 1)))) []), (.var 1)])])] ((.op ((.intOp .add)) [(.op ((.intOp .add)) [(.var 1), (.op ((.intOp ((.const 0)))) [])]), (.op ((.intOp .div)) [(.op ((.intOp ((.const 2)))) []), (.op ((.intOp .mult)) [(.var 0), (.op ((.intOp .sub)) [(.op ((.intOp ((.const 1)))) []), (.var 0)])])])]))), (.op ((.globOp ((.global 1)))) [])]), (.op ((.intOp .add)) [(.var 0), (.op ((.intOp ((.const 4)))) [])]), (.var 0), (.op ((.intOp ((.const 3)))) []), (.var 3)])))))))))) => true
  | _ => false

private def matches9 (entry : Nat × Nat × Flapjack.Compiler.Backend.Bvi.Exp) : Bool :=
  match entry with
  | (76, 3, (.let [(.op ((.intOp .sub)) [(.op ((.intOp ((.const 2)))) []), (.op (.blockOp (.elemAt 1)) [((.var 2))])])] ((.ifThenElse ((.op ((.intOp .less)) [(.op ((.intOp ((.const 0)))) []), (.var 0)])) ((.let [(.op (.blockOp (.elemAt 1)) [((.var 3))])] ((.ifThenElse ((.op ((.intOp ((.lessConstSmall 1)))) [(.var 0)])) ((.let [(.call 0 none [(.var 3), (.var 4), (.op (.blockOp (.elemAt 0)) [((.var 4))])] none)] ((.ifThenElse ((.op ((.blockOp ((.equalConst ((.int 0)))))) [(.op (.blockOp (.elemAt 1)) [((.var 0))])])) ((.call 0 none [(.var 3), (.var 0), (.op (.blockOp (.elemAt 0)) [((.var 0))])] none)) ((.call 0 ((some 72)) [(.var 3), (.var 0)] none)))))) ((.let [(.call 0 none [(.var 2), (.var 3), (.var 4), (.op (.blockOp (.elemAt 0)) [((.var 4))])] none)] ((.ifThenElse ((.op ((.blockOp ((.equalConst ((.int 0)))))) [(.op (.blockOp (.elemAt 1)) [((.var 0))])])) ((.call 0 none [(.var 0), (.op (.blockOp (.elemAt 0)) [((.var 0))])] none)) ((.call 0 ((some 72)) [(.var 0)] none)))))))))) ((.ifThenElse ((.op ((.blockOp ((.tagEq 30)))) [(.var 3)])) ((.op ((.blockOp ((.cons 31)))) [(.var 2), (.var 1), (.var 3), (.var 0), (.op ((.memOp .el)) [(.let [(.op (.blockOp (.elemAt 1)) [((.var 3))])] ((.op ((.intOp .add)) [(.op ((.intOp ((.const 1)))) []), (.op ((.intOp .div)) [(.op ((.intOp ((.const 2)))) []), (.op ((.intOp .mult)) [(.var 0), (.op ((.intOp .sub)) [(.op ((.intOp ((.const 1)))) []), (.var 0)])])])]))), (.op ((.globOp ((.global 1)))) [])])])) ((.let [(.op ((.intOp .sub)) [(.op ((.intOp ((.const 3)))) []), (.op ((.blockOp .lengthBlock)) [(.var 3)])])] ((.op ((.blockOp ((.consExtend 31)))) [(.var 3), (.var 2), (.op (.blockOp (.elemAt 2)) [((.var 4))]), (.var 1), (.op ((.memOp .el)) [(.let [(.op ((.intOp .add)) [(.var 0), (.op ((.intOp .add)) [(.op ((.intOp ((.const 2)))) []), (.var 1)])])] ((.op ((.intOp .add)) [(.op ((.intOp .add)) [(.var 1), (.op ((.intOp ((.const 1)))) [])]), (.op ((.intOp .div)) [(.op ((.intOp ((.const 2)))) []), (.op ((.intOp .mult)) [(.var 0), (.op ((.intOp .sub)) [(.op ((.intOp ((.const 1)))) []), (.var 0)])])])]))), (.op ((.globOp ((.global 1)))) [])]), (.op ((.intOp .add)) [(.var 0), (.op ((.intOp ((.const 5)))) [])]), (.var 0), (.op ((.intOp ((.const 3)))) []), (.var 4)])))))))))) => true
  | _ => false

private def matches10 (entry : Nat × Nat × Flapjack.Compiler.Backend.Bvi.Exp) : Bool :=
  match entry with
  | (80, 2, (.let [(.op (.blockOp (.elemAt 2)) [((.var 1))])] ((.call 0 none [(.var 1), (.op (.blockOp (.elemAt 3)) [((.var 2))]), (.var 0), (.op (.blockOp (.elemAt 0)) [((.var 0))])] none)))) => true
  | _ => false

private def matches11 (entry : Nat × Nat × Flapjack.Compiler.Backend.Bvi.Exp) : Bool :=
  match entry with
  | (84, 2, (.ifThenElse ((.op ((.blockOp ((.equalConst ((.int 0)))))) [(.op (.blockOp (.elemAt 1)) [((.var 1))])])) ((.let [(.call 0 none [(.op (.blockOp (.cons 0)) []), (.var 1), (.op (.blockOp (.elemAt 0)) [((.var 1))])] none)] ((.let [(.op ((.thunkOp ((.updateThunk .evaluated)))) [(.var 0), (.var 1)])] ((.var 1)))))) ((.let [(.call 0 ((some 72)) [(.op (.blockOp (.cons 0)) []), (.var 1)] none)] ((.let [(.op ((.thunkOp ((.updateThunk .evaluated)))) [(.var 0), (.var 1)])] ((.var 1)))))))) => true
  | _ => false

private def matches12 (entry : Nat × Nat × Flapjack.Compiler.Backend.Bvi.Exp) : Bool :=
  match entry with
  | (88, 0, (.let [(.call 0 ((some 62)) [(.op ((.intOp ((.const 1)))) [])] none)] ((.let [(.op ((.globOp ((.setGlobal 1)))) [(.op ((.blockOp ((.cons 0)))) [(.op ((.label 80)) [])])])] ((.call 0 ((some 92)) [] none)))))) => true
  | _ => false

private def matches13 (entry : Nat × Nat × Flapjack.Compiler.Backend.Bvi.Exp) : Bool :=
  match entry with
  | (92, 0, (.let [(.let [(.call 0 ((some 62)) [(.op ((.intOp ((.const 1)))) [])] none), (.op (.blockOp (.cons 0)) [])] ((.op ((.globOp ((.setGlobal 2)))) [(.var 1)])))] ((.call 0 ((some 96)) [] none)))) => true
  | _ => false

private def matches14 (entry : Nat × Nat × Flapjack.Compiler.Backend.Bvi.Exp) : Bool :=
  match entry with
  | (96, 0, (.let [(.let [(.call 0 ((some 73)) [] none)] (.op (.blockOp (.cons 0)) []))] ((.call 0 ((some 100)) [] none)))) => true
  | _ => false

private def matches15 (entry : Nat × Nat × Flapjack.Compiler.Backend.Bvi.Exp) : Bool :=
  match entry with
  | (73, 0, (.var 0)) => true
  | _ => false

private def matches16 (entry : Nat × Nat × Flapjack.Compiler.Backend.Bvi.Exp) : Bool :=
  match entry with
  | (100, 0, (.op ((.globOp ((.setGlobal 3)))) [(.op ((.memOp .ref)) [(.op (.blockOp (.cons 0)) [])])])) => true
  | _ => false

/-- Match every location, arity and expression in the captured BVI program. -/
def matchesCaptured (code : List (Nat × Nat × Flapjack.Compiler.Backend.Bvi.Exp)) : Bool :=
  match code with
  | [entry0, entry1, entry2, entry3, entry4, entry5, entry6, entry7, entry8, entry9, entry10, entry11, entry12, entry13, entry14, entry15, entry16] =>
      matches0 entry0 &&
      matches1 entry1 &&
      matches2 entry2 &&
      matches3 entry3 &&
      matches4 entry4 &&
      matches5 entry5 &&
      matches6 entry6 &&
      matches7 entry7 &&
      matches8 entry8 &&
      matches9 entry9 &&
      matches10 entry10 &&
      matches11 entry11 &&
      matches12 entry12 &&
      matches13 entry13 &&
      matches14 entry14 &&
      matches15 entry15 &&
      matches16 entry16
  | _ => false

end Flapjack.Test.BvlInlineCakeBviOracle
