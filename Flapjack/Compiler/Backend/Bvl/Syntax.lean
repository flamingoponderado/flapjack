import Flapjack.Compiler.Backend.ClosLang.Syntax

namespace Flapjack.Compiler.Backend.Bvl

/-- Complete original expression syntax; the operation payload is the actual
ClosLang.Op carrier. Every recursive List/Option and numeric payload is retained. -/
@[hol "cakeml/compiler/backend/bvlScript.sml" "exp"]
inductive Exp where
  | var : Nat → Exp
  | ifThenElse : Exp → Exp → Exp → Exp
  | «let» : List Exp → Exp → Exp
  | raise : Exp → Exp
  | handle : Exp → Exp → Exp
  | tick : Exp → Exp
  | call : Nat → Option Nat → List Exp → Exp
  | force : Nat → Nat → Exp
  | op : ClosLang.Op → List Exp → Exp

/-- Apply the BVL tick constructor repeatedly. -/
@[hol "cakeml/compiler/backend/bvlScript.sml" "mk_tick_def"]
def mkTick : Nat → Exp → Exp
  | 0, e => e
  | n + 1, e => .tick (mkTick n e)

end Flapjack.Compiler.Backend.Bvl
