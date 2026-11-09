import Flapjack.Compiler.Backend.ClosAnnotate.Free

/-! Re-index variables after closure free-variable discovery. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open ClosLang

/-- Resolve a variable outside the local binder prefix through the sparse map.
The source leaves its first, unused parameter polymorphic. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "get_var_def"]
def getVar {α : Type} (_m : α) (l : Nat) (i : Spt Nat) (v : Nat) : Nat :=
  if v < l then v else l + (sptLookup (v - l) i).getD 0

/-- Build the source's right-recursive map from old names to compact indices. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "shifted_env_def"]
def shiftedEnv : Nat → List Nat → Spt Nat
  | _, [] => .ln
  | n, x :: xs => sptInsert x n (shiftedEnv (n + 1) xs)

mutual
/-- Re-index one annotated closure expression. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "shift_sing_def"]
def shiftSing : Exp → Nat → Nat → Spt Nat → Exp
  | .var t v, m, l, i => .var t (getVar m l i v)
  | .ifThenElse t x y z, m, l, i =>
      .ifThenElse t (shiftSing x m l i) (shiftSing y m l i) (shiftSing z m l i)
  | .let t xs x, m, l, i => .let t (shiftList xs m l i) (shiftSing x m (l + xs.length) i)
  | .raise t x, m, l, i => .raise t (shiftSing x m l i)
  | .tick t x, m, l, i => .tick t (shiftSing x m l i)
  | .op t op xs, m, l, i => .op t op (shiftList xs m l i)
  | .app t loc x xs, m, l, i => .app t loc (shiftSing x m l i) (shiftList xs m l i)
  | .fn name loc vs args x, m, l, i =>
      let k := m + l
      let live := (vs.getD []).filter (· < k)
      let vars := live.map (getVar m l i)
      .fn name loc (some vars) args (shiftSing x k args (shiftedEnv 0 live))
  | .letrec names loc vs fs x, m, l, i =>
      let k := m + l
      let live := (vs.getD []).filter (· < k)
      let vars := live.map (getVar m l i)
      let cs := shiftFuns fs.length k (shiftedEnv 0 live) fs
      .letrec names loc (some vars) cs (shiftSing x m (l + fs.length) i)
  | .handle t x y, m, l, i => .handle t (shiftSing x m l i) (shiftSing y m (l + 1) i)
  | .call t ticks dest xs, m, l, i => .call t ticks dest (shiftList xs m l i)

/-- Re-index a list of closure expressions. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "shift_sing_def"]
def shiftList : List Exp → Nat → Nat → Spt Nat → List Exp
  | [], _, _, _ => []
  | x :: xs, m, l, i => shiftSing x m l i :: shiftList xs m l i

/-- Re-index the bodies of a recursive closure group. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "shift_sing_def"]
def shiftFuns (fnsLen k : Nat) (newI : Spt Nat) : List (Nat × Exp) → List (Nat × Exp)
  | [] => []
  | (n, x) :: xs => (n, shiftSing x k (n + fnsLen) newI) :: shiftFuns fnsLen k newI xs
end

/-- Annotate a single expression using free-variable discovery and shifting. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "annotate_sing_def"]
def annotateSing (arity : Nat) (x : Exp) : Exp := shiftSing (altFreeSing x).1 0 arity .ln

/-- Annotate a list using the original combined free-variable traversal. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "annotate_list_def"]
def annotateList (arity : Nat) (xs : List Exp) : List Exp := shiftList (altFreeList xs).1 0 arity .ln

/-- Executable optimized annotation of labeled closure functions. HOL's
`compile_def` uses the separate list-shaped `annotate` and its singleton
head; `compileSource_eq_compile` proves that source definition agrees with
this traversal. -/
def compile {α : Type} (prog : List (α × Nat × Exp)) : List (α × Nat × Exp) :=
  prog.map (fun (n, args, exp) => (n, args, annotateSing args exp))

/-- Executable optimized annotation of an incremental program. HOL's
`compile_inc_def` uses the separate source `annotate` and `compile`;
`compileIncSource_eq_compileInc` proves agreement with this traversal. -/
def compileInc {α : Type} (p : List Exp × List (α × Nat × Exp)) : List Exp × List (α × Nat × Exp) :=
  (annotateList 0 p.1, compile p.2)

end Flapjack.Compiler.Backend.ClosAnnotate
