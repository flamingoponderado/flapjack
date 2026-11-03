import Flapjack.Compiler.Backend.ClosLang.Syntax

/-! Source-shaped total traversal for closure tick removal. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open ClosLang

mutual
/-- Remove ticks and reset call tick counts, retaining the other annotations. -/
@[hol "cakeml/compiler/backend/clos_ticksScript.sml" "remove_ticks_sing_def"]
def removeSing : Exp → Exp
  | .var t v => .var t v
  | .ifThenElse t x y z => .ifThenElse t (removeSing x) (removeSing y) (removeSing z)
  | .let t xs body => .let t (removeList xs) (removeSing body)
  | .raise t x => .raise t (removeSing x)
  | .handle t x y => .handle t (removeSing x) (removeSing y)
  | .op t op xs => .op t op (removeList xs)
  | .tick _ x => removeSing x
  | .call t _ dest xs => .call t 0 dest (removeList xs)
  | .app t loc x xs => .app t loc (removeSing x) (removeList xs)
  | .fn name loc vs arity body => .fn name loc vs arity (removeSing body)
  | .letrec names loc vs fns body => .letrec names loc vs (removeFuns fns) (removeSing body)

/-- Process expressions in their original order. -/
@[hol "cakeml/compiler/backend/clos_ticksScript.sml" "remove_ticks_sing_def"]
def removeList : List Exp → List Exp
  | [] => []
  | x :: xs => removeSing x :: removeList xs

/-- Process recursive function bodies without changing their arities. -/
@[hol "cakeml/compiler/backend/clos_ticksScript.sml" "remove_ticks_sing_def"]
def removeFuns : List (Nat × Exp) → List (Nat × Exp)
  | [] => []
  | (arity, body) :: rest => (arity, removeSing body) :: removeFuns rest
end

end Flapjack.Compiler.Backend.ClosTicks
