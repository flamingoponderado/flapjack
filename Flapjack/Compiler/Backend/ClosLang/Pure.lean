import Flapjack.Compiler.Backend.ClosLang.Syntax

/-! Purity classification used by closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosLang

/-- Classify operations that cannot raise or modify state. -/
@[hol "cakeml/compiler/backend/closLangScript.sml" "pure_op_def"]
def pureOp : Op → Bool
  | .ffi _ | .globOp (.setGlobal _) | .globOp .allocGlobal | .memOp (.refByte _)
  | .memOp .refArray | .memOp .updateByte | .memOp (.copyByte false) | .memOp .xorByte
  | .memOp .ref | .memOp .update | .install | .thunkOp _ => false
  | _ => true

mutual
/-- Classify a closure expression using the source's conservative clauses. -/
@[hol "cakeml/compiler/backend/closLangScript.sml" "pure_def"]
def pure : Exp → Bool
  | .var _ _ | .fn _ _ _ _ _ => true
  | .ifThenElse _ x y z => pure x && pure y && pure z
  | .let _ xs x => pureList xs && pure x
  | .handle _ x _ => pure x
  | .letrec _ _ _ _ x => pure x
  | .op _ op xs => pureList xs && pureOp op
  | .raise _ _ | .tick _ _ | .call _ _ _ _ | .app _ _ _ _ => false

/-- Apply the source's `EVERY pure` to an expression list. -/
def pureList : List Exp → Bool
  | [] => true
  | x :: xs => pure x && pureList xs
end

end Flapjack.Compiler.Backend.ClosLang
