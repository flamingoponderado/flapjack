import Flapjack.Compiler.Backend.ClosLang.Pure
import Flapjack.Compiler.Backend.DbVars

/-! Free-variable discovery and closure annotations. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open ClosLang DbVars

/-- A source zero expression with the original trace annotation. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "const_0_def"]
def const0 (t : BackendCommon.Tra) : Exp := .op t (.intOp (.const 0)) []

/-- Check that none of the first `n` variables occurs in a set expression. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "no_overlap_def"]
def noOverlap : Nat → DbVarSet → Bool
  | 0, _ => true
  | n + 1, s => !hasVar n s && noOverlap n s

mutual
/-- Annotate free variables in one expression and remove unused pure lets. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "alt_free_sing_def"]
def altFreeSing : Exp → Exp × DbVarSet
  | .var t v => (.var t v, .var v)
  | .ifThenElse t x y z =>
      let (x, a) := altFreeSing x
      let (y, b) := altFreeSing y
      let (z, c) := altFreeSing z
      (.ifThenElse t x y z, mkUnion a (mkUnion b c))
  | .let t xs body =>
      let (body, live) := altFreeSing body
      if noOverlap xs.length live && pureList xs then
        (.let t (List.replicate xs.length (const0 t)) body, .shift xs.length live)
      else
        let (xs, argsLive) := altFreeList xs
        (.let t xs body, mkUnion argsLive (.shift xs.length live))
  | .raise t x => let (x, live) := altFreeSing x; (.raise t x, live)
  | .tick t x => let (x, live) := altFreeSing x; (.tick t x, live)
  | .op t op xs => let (xs, live) := altFreeList xs; (.op t op xs, live)
  | .app t loc x xs =>
      let (x, a) := altFreeSing x
      let (xs, b) := altFreeList xs
      (.app t loc x xs, mkUnion a b)
  | .fn name loc _ arity body =>
      let (body, live) := altFreeSing body
      let live := DbVarSet.shift arity live
      (.fn name loc (some (varsToList live)) arity body, live)
  | .letrec names loc _ fs body =>
      let (body, bodyLive) := altFreeSing body
      let fs := altFreeFuns fs.length fs
      let live := listMkUnion (fs.map Prod.snd)
      (.letrec names loc (some (varsToList live)) (fs.map Prod.fst) body,
        mkUnion live (.shift fs.length bodyLive))
  | .handle t x y =>
      let (x, a) := altFreeSing x
      let (y, b) := altFreeSing y
      (.handle t x y, mkUnion a (.shift 1 b))
  | .call t ticks dest xs => let (xs, live) := altFreeList xs; (.call t ticks dest xs, live)

/-- Traverse a list and combine free variables in source order. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "alt_free_sing_def"]
def altFreeList : List Exp → List Exp × DbVarSet
  | [] => ([], .empty)
  | x :: xs =>
      let (x, a) := altFreeSing x
      let (xs, b) := altFreeList xs
      (x :: xs, mkUnion a b)

/-- Annotate recursive bodies, shifting each free set by its binders. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "alt_free_sing_def"]
def altFreeFuns (m : Nat) : List (Nat × Exp) → List ((Nat × Exp) × DbVarSet)
  | [] => []
  | (n, e) :: xs =>
      let (e, live) := altFreeSing e
      ((n, e), .shift (n + m) live) :: altFreeFuns m xs
end

end Flapjack.Compiler.Backend.ClosAnnotate
