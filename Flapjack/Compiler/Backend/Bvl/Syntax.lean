import Flapjack.Compiler.Backend.ClosLang.Syntax

namespace Flapjack.Compiler.Backend.Bvl

/-- Complete original expression syntax; the operation payload is the actual
ClosLang.Op carrier. Every recursive List/Option and numeric payload is retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
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

end Flapjack.Compiler.Backend.Bvl
