import Flapjack.Compiler.Backend.ClosLang.Syntax
import Flapjack.AstHOL.GeneratedSize
import Flapjack.Compiler.Backend.BackendCommon.Trace.GeneratedSize
import Flapjack.Misc.List.Size
import Flapjack.Misc.GeneratedSize

/-! Datatype-generated sizes needed by closure-value proofs. -/
namespace Flapjack.Compiler.Backend.ClosLang
open Flapjack

mutual
/-- Datatype-generated HOL constant size, including nested constants. -/
def constSizeHOL : Const → Nat
  | .constCons n xs => 1 + (n + constListSizeHOL xs)
  | .constInt _ => 1
  | .constStr s => 1 + mlstringSizeHOL s
  | .constWord64 w => 1 + w.toNat
/-- List component of HOL constant size. -/
def constListSizeHOL : List Const → Nat
  | [] => 0
  | x :: xs => 1 + (constSizeHOL x + constListSizeHOL xs)
end

/-- Datatype-generated HOL constant-part size. -/
def constPartSizeHOL : ConstPart → Nat
  | .con n xs => 1 + (n + listSizeHOL id xs)
  | .int _ => 1
  | .str s => 1 + mlstringSizeHOL s
  | .w64 w => 1 + w.toNat

/-- Datatype-generated HOL integer-operation size. -/
def intOpSizeHOL : IntOp → Nat
  | .const _ => 1
  | .lessConstSmall n => 1 + n
  | _ => 0

/-- Datatype-generated HOL word-operation size. -/
def wordOpSizeHOL : WordOp → Nat
  | .wordOpw _ _ => 1
  | .wordShift _ _ n => 1 + n
  | .wordTest _ test => 1 + AstHOL.testSizeHOL test
  | .wordFromInt | .wordToInt => 0
  | .wordFromWord _ | .fpCmp _ | .fpUop _ | .fpBop _ | .fpTop _ => 1

/-- Datatype-generated HOL block-operation size. -/
def blockOpSizeHOL : BlockOp → Nat
  | .cons n | .elemAt n | .lenEq n | .tagEq n | .consExtend n | .fromList n => 1 + n
  | .tagLenEq n m => 1 + (n + m)
  | .boolTest t => 1 + AstHOL.testSizeHOL t
  | .constant c => 1 + constSizeHOL c
  | .equalConst c => 1 + constPartSizeHOL c
  | .build cs => 1 + listSizeHOL constPartSizeHOL cs
  | _ => 0

/-- Datatype-generated HOL global-operation size. -/
def globOpSizeHOL : GlobOp → Nat
  | .global n | .setGlobal n => 1 + n
  | _ => 0

/-- Datatype-generated HOL memory-operation size. -/
def memOpSizeHOL : MemOp → Nat
  | .refByte _ | .copyByte _ | .stringCmp _ _ | .boundsCheckByte _ => 1
  | .mutCons n m => 1 + (n + m)
  | _ => 0

/-- Datatype-generated HOL closure-operation size. -/
def opSizeHOL : Op → Nat
  | .label n => 1 + n
  | .ffi name => 1 + mlstringSizeHOL name
  | .intOp op => 1 + intOpSizeHOL op
  | .wordOp op => 1 + wordOpSizeHOL op
  | .blockOp op => 1 + blockOpSizeHOL op
  | .globOp op => 1 + globOpSizeHOL op
  | .memOp op => 1 + memOpSizeHOL op
  | .install => 0
  | .thunkOp op => 1 + AstHOL.thunkOpSizeHOL op

mutual
/-- Datatype-generated HOL closure-expression size. -/
def expSizeHOL : Exp → Nat
  | .var tr n => 1 + (BackendCommon.traSizeHOL tr + n)
  | .ifThenElse tr a b c => 1 + (BackendCommon.traSizeHOL tr + (expSizeHOL a + (expSizeHOL b + expSizeHOL c)))
  | .let tr xs b => 1 + (BackendCommon.traSizeHOL tr + (expListSizeHOL xs + expSizeHOL b))
  | .raise tr b | .tick tr b => 1 + (BackendCommon.traSizeHOL tr + expSizeHOL b)
  | .handle tr a b => 1 + (BackendCommon.traSizeHOL tr + (expSizeHOL a + expSizeHOL b))
  | .call tr a b xs => 1 + (BackendCommon.traSizeHOL tr + (a + (b + expListSizeHOL xs)))
  | .app tr loc b xs => 1 + (BackendCommon.traSizeHOL tr + (optionSizeHOL id loc + (expSizeHOL b + expListSizeHOL xs)))
  | .fn name loc vs n b => 1 + (mlstringSizeHOL name + (optionSizeHOL id loc + (optionSizeHOL (listSizeHOL id) vs + (n + expSizeHOL b))))
  | .letrec names loc vs fns b => 1 + (listSizeHOL mlstringSizeHOL names + (optionSizeHOL id loc + (optionSizeHOL (listSizeHOL id) vs + (expFunsSizeHOL fns + expSizeHOL b))))
  | .op tr op xs => 1 + (BackendCommon.traSizeHOL tr + (opSizeHOL op + expListSizeHOL xs))
/-- HOL exp1_size, for recursive function groups. -/
def expFunsSizeHOL : List (Nat × Exp) → Nat
  | [] => 0
  | (n, e) :: xs => 1 + ((1 + (n + expSizeHOL e)) + expFunsSizeHOL xs)
/-- HOL exp3_size, for expression lists. -/
def expListSizeHOL : List Exp → Nat
  | [] => 0
  | e :: es => 1 + (expSizeHOL e + expListSizeHOL es)
end
end Flapjack.Compiler.Backend.ClosLang
