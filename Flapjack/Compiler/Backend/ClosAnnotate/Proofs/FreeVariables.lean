import Flapjack.Compiler.Backend.ClosAnnotate.Free.SourceEquations

/-! Free-variable observations for the closure-annotation simulation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open ClosLang DbVars

/-- Observe the optimized free-variable pass at one de Bruijn index. The
source-shaped `altFree` equations are checked in `Free.SourceEquations`;
this observation remains untagged until source correspondence is reviewed. -/
def altFv (index : Nat) (expressions : List Exp) : Bool :=
  hasVar index (altFree expressions).2

private theorem mkUnion_empty_right (set : DbVarSet) : mkUnion set .empty = set := by
  cases set <;> rfl

/-- Membership in the optimized union is disjunction, including empty sets. -/
theorem hasVar_mkUnion (index : Nat) (left right : DbVarSet) :
    hasVar index (mkUnion left right) = (hasVar index left || hasVar index right) := by
  cases left <;> cases right <;> simp [mkUnion, hasVar]

/-- The free variables of a list combine its singleton head and tail. -/
theorem altFv_cons (index : Nat) (first : Exp) (rest : List Exp) :
    altFv index (first :: rest) = (altFv index [first] || altFv index rest) := by
  simp [altFv, altFree, altFreeList, mkUnion_empty_right, hasVar_mkUnion]

/-- An empty expression list has no free variables. -/
theorem altFv_nil (index : Nat) : altFv index [] = false := rfl

/-- A variable expression contains exactly its own de Bruijn index. -/
theorem altFv_var (index varIndex : Nat) (trace : BackendCommon.Tra) :
    altFv index [.var trace varIndex] = (index == varIndex) := by
  simp [altFv, altFree, altFreeList, altFreeSing, hasVar, mkUnion_empty_right]

/-- Conditionals combine observations of their three arms. -/
theorem altFv_if (index : Nat) (trace : BackendCommon.Tra) (condition yes no : Exp) :
    altFv index [.ifThenElse trace condition yes no] =
      (altFv index [condition] || (altFv index [yes] || altFv index [no])) := by
  simp [altFv, altFree, altFreeList, altFreeSing, mkUnion_empty_right, hasVar_mkUnion]

/-- Raise and tick preserve the free-variable set of their body. -/
theorem altFv_raise (index : Nat) (trace : BackendCommon.Tra) (body : Exp) :
    altFv index [.raise trace body] = altFv index [body] := by
  simp [altFv, altFree, altFreeList, altFreeSing, mkUnion_empty_right]

theorem altFv_tick (index : Nat) (trace : BackendCommon.Tra) (body : Exp) :
    altFv index [.tick trace body] = altFv index [body] := by
  simp [altFv, altFree, altFreeList, altFreeSing, mkUnion_empty_right]

/-- Primitive and direct-call expressions use their arguments' free variables. -/
theorem altFv_op (index : Nat) (trace : BackendCommon.Tra) (op : Op) (args : List Exp) :
    altFv index [.op trace op args] = altFv index args := by
  simp [altFv, altFree, altFreeList, altFreeSing, mkUnion_empty_right]

theorem altFv_call (index : Nat) (trace : BackendCommon.Tra) (ticks location : Nat) (args : List Exp) :
    altFv index [.call trace ticks location args] = altFv index args := by
  simp [altFv, altFree, altFreeList, altFreeSing, mkUnion_empty_right]

/-- Applications combine the function and argument observations. -/
theorem altFv_app (index : Nat) (trace : BackendCommon.Tra) (location : Option Nat)
    (function : Exp) (args : List Exp) :
    altFv index [.app trace location function args] = (altFv index [function] || altFv index args) := by
  simp [altFv, altFree, altFreeList, altFreeSing, mkUnion_empty_right, hasVar_mkUnion]

/-- Closure bodies shift free-variable indices past their formal parameters. -/
theorem altFv_fn (index : Nat) (name : Flapjack.Basis.Pure.MlString.MlString)
    (location : Option Nat) (vars : Option (List Nat)) (arity : Nat) (body : Exp) :
    altFv index [.fn name location vars arity body] = altFv (index + arity) [body] := by
  simp [altFv, altFree, altFreeList, altFreeSing, mkUnion_empty_right, hasVar]

/-- A handler binds its exception value before evaluating its second arm. -/
theorem altFv_handle (index : Nat) (trace : BackendCommon.Tra) (body handler : Exp) :
    altFv index [.handle trace body handler] =
      (altFv index [body] || altFv (index + 1) [handler]) := by
  simp [altFv, altFree, altFreeList, altFreeSing, mkUnion_empty_right, hasVar_mkUnion, hasVar]

/-- Unused pure bindings are erased; otherwise their free variables are
included alongside those of the body after its binders. -/
theorem altFv_let (index : Nat) (trace : BackendCommon.Tra) (bindings : List Exp) (body : Exp) :
    altFv index [.let trace bindings body] =
      if noOverlap bindings.length (altFreeList [body]).2 && pureList bindings then
        altFv (index + bindings.length) [body]
      else altFv index bindings || altFv (index + bindings.length) [body] := by
  simp only [altFv, altFree, altFreeList, mkUnion_empty_right, altFreeSing]
  split <;> simp [hasVar_mkUnion, hasVar, altFreeList_length]

private theorem hasVar_altFreeFuns (index count : Nat) (functions : List (Nat × Exp)) :
    hasVar index (listMkUnion ((altFreeFuns count functions).map Prod.snd)) =
      functions.any (fun (arity, body) => altFv (index + arity + count) [body]) := by
  induction functions with
  | nil => rfl
  | cons function rest ih =>
    obtain ⟨arity, body⟩ := function
    simp [altFreeFuns, listMkUnion, hasVar_mkUnion, hasVar, altFv, altFree, altFreeList,
      mkUnion_empty_right, ih, Nat.add_assoc]

/-- The live set computed for a recursive function group contains exactly
the variables used by one of its bodies beyond its binders. -/
theorem hasVar_recursiveLive (index count : Nat) (functions : List (Nat × Exp)) :
    hasVar index (listMkUnion ((altFreeFuns count functions).map Prod.snd)) =
      functions.any (fun (arity, body) => altFv (index + arity + count) [body]) :=
  hasVar_altFreeFuns index count functions

/-- Recursive function bodies shift past both their arguments and the whole
function bundle; the enclosing body shifts past that bundle. -/
theorem altFv_letrec (index : Nat) (names : List Flapjack.Basis.Pure.MlString.MlString)
    (location : Option Nat) (vars : Option (List Nat)) (functions : List (Nat × Exp)) (body : Exp) :
    altFv index [.letrec names location vars functions body] =
      (functions.any (fun (arity, body) => altFv (index + arity + functions.length) [body]) ||
        altFv (index + functions.length) [body]) := by
  simp [altFv, altFree, altFreeList, altFreeSing, mkUnion_empty_right, hasVar_mkUnion,
    hasVar, hasVar_altFreeFuns, altFreeFuns_length]

end Flapjack.Compiler.Backend.ClosAnnotate
