import Flapjack.Misc.Sptree

/-! De Bruijn variable sets used for closure annotations. -/
namespace Flapjack.Compiler.Backend.DbVars

/-- A compact variable-set expression, retaining shifts and unions. -/
@[hol "cakeml/compiler/backend/db_varsScript.sml" "db_var_set"]
inductive DbVarSet where
  | empty
  | var : Nat → DbVarSet
  | shift : Nat → DbVarSet → DbVarSet
  | union : DbVarSet → DbVarSet → DbVarSet

/-- Construct a union while removing empty children. -/
@[hol "cakeml/compiler/backend/db_varsScript.sml" "mk_Union_def"]
def mkUnion : DbVarSet → DbVarSet → DbVarSet
  | .empty, y => y
  | x, .empty => x
  | x, y => .union x y

/-- Right-fold unions in the source's order. -/
@[hol "cakeml/compiler/backend/db_varsScript.sml" "list_mk_Union_def"]
def listMkUnion : List DbVarSet → DbVarSet
  | [] => .empty
  | x :: xs => mkUnion x (listMkUnion xs)

/-- Accumulate visible variables in the source's sparse-tree representation. -/
@[hol "cakeml/compiler/backend/db_varsScript.sml" "db_to_set_acc_def"]
def dbToSetAcc : Nat → DbVarSet → NumSet → NumSet
  | _, .empty, s => s
  | n, .var v, s => if v < n then s else sptInsert (v - n) () s
  | n, .shift k d, s => dbToSetAcc (n + k) d s
  | n, .union a b, s => dbToSetAcc n a (dbToSetAcc n b s)

/-- Materialize a variable-set expression as a sparse tree. -/
@[hol "cakeml/compiler/backend/db_varsScript.sml" "db_to_set_def"]
def dbToSet (db : DbVarSet) : NumSet := dbToSetAcc 0 db .ln

/-- Enumerate variables in HOL sparse-tree traversal order. -/
@[hol "cakeml/compiler/backend/db_varsScript.sml" "vars_to_list_def"]
def varsToList (db : DbVarSet) : List Nat := (sptToAList (dbToSet db)).map Prod.fst

/-- Build a variable-set expression from a list, in source fold order. -/
@[hol "cakeml/compiler/backend/db_varsScript.sml" "vars_from_list_def"]
def varsFromList (vs : List Nat) : DbVarSet := vs.foldl (fun s v => .union (.var v) s) .empty

/-- Flatten a variable-set expression through the source tree enumeration. -/
@[hol "cakeml/compiler/backend/db_varsScript.sml" "vars_flatten_def"]
def varsFlatten (db : DbVarSet) : DbVarSet := varsFromList (varsToList db)

/-- Test membership directly in a variable-set expression. -/
@[hol "cakeml/compiler/backend/db_varsScript.sml" "has_var_def"]
def hasVar : Nat → DbVarSet → Bool
  | _, .empty => false
  | n, .var v => n == v
  | n, .shift k d => hasVar (n + k) d
  | n, .union a b => hasVar n a || hasVar n b

end Flapjack.Compiler.Backend.DbVars
