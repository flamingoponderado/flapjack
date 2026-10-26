import Flapjack.Compiler.Backend.ClosLang.Syntax
import Flapjack.NamespaceHOL

/-! Imperative data-language syntax and allocation classifications. -/
namespace Flapjack.Compiler.Backend.DataLang

/-- Source data-language programs, retaining the optional live-name sets on
calls, assignments and force operations. -/
@[hol "cakeml/compiler/backend/dataLangScript.sml" "prog"]
inductive Prog where
  | skip
  | move : Nat → Nat → Prog
  | call : Option (List Nat × NumSet) → Option Nat → List Nat → Option (Nat × Prog) → Prog
  | assign : Nat → ClosLang.Op → List Nat → Option NumSet → Prog
  | seq : Prog → Prog → Prog
  | ifThenElse : Nat → Prog → Prog → Prog
  | makeSpace : Nat → NumSet → Prog
  | raise : Nat → Prog
  | «return» : List Nat → Prog
  | tick
  | force : Option (Nat × NumSet) → Nat → Nat → Prog

/-- Whether an operation may reset the allocation-space accounting. -/
@[hol "cakeml/compiler/backend/dataLangScript.sml" "op_space_reset_def"]
def opSpaceReset : ClosLang.Op → Bool
  | .intOp .add | .intOp .sub | .intOp .mult | .intOp .div | .intOp .mod
  | .intOp .less | .intOp .lessEq | .intOp .greater | .intOp .greaterEq
  | .blockOp .equal | .blockOp .listAppend | .blockOp (.fromList _)
  | .blockOp (.consExtend _) | .memOp .refArray | .memOp (.refByte _)
  | .memOp .configGC | .ffi _ => true
  | .memOp (.copyByte flag) => flag
  | _ => false

/-- Whether the operation requires an explicit live-name set. -/
@[hol "cakeml/compiler/backend/dataLangScript.sml" "op_requires_names_def"]
def opRequiresNames (op : ClosLang.Op) : Bool :=
  opSpaceReset op || match op with
    | .ffi _ | .install | .memOp (.copyByte _) | .memOp .xorByte
    | .memOp (.stringCmp _ _) => true
    | _ => false

/-- Prefix a program with the indicated number of ticks. -/
@[hol "cakeml/compiler/backend/dataLangScript.sml" "mk_ticks_def"]
def mkTicks : Nat → Prog → Prog
  | 0, p => p
  | n + 1, p => .seq .tick (mkTicks n p)

end Flapjack.Compiler.Backend.DataLang
