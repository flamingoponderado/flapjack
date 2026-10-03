import Flapjack.AstHOL.BackendOperators
import Flapjack.Basis.Pure.MlString
import Flapjack.Compiler.Backend.BackendCommon.Trace
import Flapjack.Compiler.Backend.BackendCommon.Operators
import Flapjack.FpSemHOL

namespace Flapjack.Compiler.Backend.ClosLang

open Flapjack.Basis.Pure.MlString

/-! Complete source syntax carriers. HOL word64 payloads are fixed BitVec 64,
not a variable-width substitute. All names use native MlString. FP payloads
are the exact operation enums, without importing an evaluator into the syntax.
Lists retain their literal order and recursive payloads, including Letrec pairs. -/

/-- Complete original `const` datatype, preserving every constructor and payload. -/
@[hol "cakeml/compiler/backend/closLangScript.sml" "const"]
inductive Const where
  | constCons : Nat → List Const → Const
  | constInt : Int → Const
  | constStr : MlString → Const
  | constWord64 : BitVec 64 → Const

/-- Complete original `const_part` datatype, preserving every constructor and payload. -/
@[hol "cakeml/compiler/backend/closLangScript.sml" "const_part"]
inductive ConstPart where
  | con : Nat → List Nat → ConstPart
  | int : Int → ConstPart
  | str : MlString → ConstPart
  | w64 : BitVec 64 → ConstPart

/-- Complete original `int_op` datatype, preserving every constructor and payload. -/
@[hol "cakeml/compiler/backend/closLangScript.sml" "int_op"]
inductive IntOp where
  | const : Int → IntOp
  | add
  | sub
  | mult
  | div
  | mod
  | less
  | lessEq
  | greater
  | greaterEq
  | lessConstSmall : Nat → IntOp

/-- Complete original `word_op` datatype, preserving every constructor and payload. -/
@[hol "cakeml/compiler/backend/closLangScript.sml" "word_op"]
inductive WordOp where
  | wordOpw : AstHOL.WordSize → BackendCommon.Opw → WordOp
  | wordShift : AstHOL.WordSize → Shift → Nat → WordOp
  | wordTest : AstHOL.WordSize → AstHOL.Test → WordOp
  | wordFromInt
  | wordToInt
  | wordFromWord : Bool → WordOp
  | fpCmp : FpCmp → WordOp
  | fpUop : FpUop → WordOp
  | fpBop : FpBop → WordOp
  | fpTop : FpTop → WordOp

/-- Complete original `block_op` datatype, preserving every constructor and payload. -/
@[hol "cakeml/compiler/backend/closLangScript.sml" "block_op"]
inductive BlockOp where
  | cons : Nat → BlockOp
  | elemAt : Nat → BlockOp
  | tagLenEq : Nat → Nat → BlockOp
  | lenEq : Nat → BlockOp
  | tagEq : Nat → BlockOp
  | lengthBlock
  | boolTest : AstHOL.Test → BlockOp
  | boolNot
  | boundsCheckBlock
  | consExtend : Nat → BlockOp
  | fromList : Nat → BlockOp
  | listAppend
  | constant : Const → BlockOp
  | equal
  | equalConst : ConstPart → BlockOp
  | build : List ConstPart → BlockOp

/-- Complete original `glob_op` datatype, preserving every constructor and payload. -/
@[hol "cakeml/compiler/backend/closLangScript.sml" "glob_op"]
inductive GlobOp where
  | global : Nat → GlobOp
  | setGlobal : Nat → GlobOp
  | allocGlobal
  | globalsPtr
  | setGlobalsPtr

/-- Complete original `mem_op` datatype, preserving every constructor and payload. -/
@[hol "cakeml/compiler/backend/closLangScript.sml" "mem_op"]
inductive MemOp where
  | ref
  | update
  | el
  | length
  | lengthByte
  | refByte : Bool → MemOp
  | refArray
  | derefByte
  | updateByte
  | concatByteVec
  | copyByte : Bool → MemOp
  | fromListByte
  | toListByte
  | lengthByteVec
  | derefByteVec
  | stringCmp : Bool → Opb → MemOp
  | xorByte
  | boundsCheckArray
  | boundsCheckByte : Bool → MemOp
  | mutCons : Nat → Nat → MemOp
  | updateCons
  | finaliseCons
  | configGC

/-- Complete original `op` datatype, preserving every constructor and payload. -/
@[hol "cakeml/compiler/backend/closLangScript.sml" "op"]
inductive Op where
  | label : Nat → Op
  | ffi : MlString → Op
  | intOp : IntOp → Op
  | wordOp : WordOp → Op
  | blockOp : BlockOp → Op
  | globOp : GlobOp → Op
  | memOp : MemOp → Op
  | install
  | thunkOp : AstHOL.ThunkOp → Op

/-- Complete original `exp` datatype, preserving every constructor and payload. -/
@[hol "cakeml/compiler/backend/closLangScript.sml" "exp"]
inductive Exp where
  | var : BackendCommon.Tra → Nat → Exp
  | ifThenElse : BackendCommon.Tra → Exp → Exp → Exp → Exp
  | «let» : BackendCommon.Tra → List Exp → Exp → Exp
  | raise : BackendCommon.Tra → Exp → Exp
  | handle : BackendCommon.Tra → Exp → Exp → Exp
  | tick : BackendCommon.Tra → Exp → Exp
  | call : BackendCommon.Tra → Nat → Nat → List Exp → Exp
  | app : BackendCommon.Tra → Option Nat → Exp → List Exp → Exp
  | fn : MlString → Option Nat → Option (List Nat) → Nat → Exp → Exp
  | letrec : List MlString → Option Nat → Option (List Nat) → List (Nat × Exp) → Exp → Exp
  | op : BackendCommon.Tra → Op → List Exp → Exp

end Flapjack.Compiler.Backend.ClosLang
