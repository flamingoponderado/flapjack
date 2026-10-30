import Flapjack.Compiler.Backend.ClosLang.Syntax
import Flapjack.Compiler.Backend.FlatProps.Globals

/-! Closure-language global initialization bags and closure safety. -/
namespace Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.FlatProps (GlobalBag emptyGlobalBag unionGlobalBag)

/-- A SetGlobal operation contributes one initialization of its index. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "op_gbag_def"]
def opGlobalBag : ClosLang.Op → GlobalBag
  | .globOp (.setGlobal index) => fun key => if key = index then 1 else 0
  | _ => emptyGlobalBag

mutual
/-- Multiplicity of global writes in a closure expression. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "set_globals_def"]
def setGlobals : ClosLang.Exp → GlobalBag
  | .var .. => emptyGlobalBag
  | .ifThenElse _ a b c => unionGlobalBag (unionGlobalBag (setGlobals a) (setGlobals b)) (setGlobals c)
  | .let _ bindings body => unionGlobalBag (setGlobals body) (elistGlobals bindings)
  | .raise _ body | .tick _ body | .fn _ _ _ _ body => setGlobals body
  | .handle _ a b => unionGlobalBag (setGlobals a) (setGlobals b)
  | .call _ _ _ args => elistGlobals args
  | .app _ _ fn args => unionGlobalBag (setGlobals fn) (elistGlobals args)
  | .letrec _ _ _ bindings body => unionGlobalBag (setGlobals body) (funGlobals bindings)
  | .op _ op args => unionGlobalBag (opGlobalBag op) (elistGlobals args)
termination_by exp => sizeOf exp

/-- Global writes across a closure expression list. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "set_globals_def"]
def elistGlobals : List ClosLang.Exp → GlobalBag
  | [] => emptyGlobalBag
  | e :: es => unionGlobalBag (setGlobals e) (elistGlobals es)
termination_by es => sizeOf es

/-- Flapjack helper for the source's mapped recursive-function bodies. -/
def funGlobals : List (Nat × ClosLang.Exp) → GlobalBag
  | [] => emptyGlobalBag
  | (_, body) :: rest => unionGlobalBag (setGlobals body) (funGlobals rest)
termination_by fs => sizeOf fs
end

mutual
/-- No closure body captures a global write. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "esgc_free_def" 1836]
def esgcFree : ClosLang.Exp → Prop
  | .var .. => True
  | .ifThenElse _ a b c => esgcFree a ∧ esgcFree b ∧ esgcFree c
  | .let _ bindings body => esgcFreeList bindings ∧ esgcFree body
  | .raise _ body | .tick _ body => esgcFree body
  | .handle _ a b => esgcFree a ∧ esgcFree b
  | .call _ _ _ args | .op _ _ args => esgcFreeList args
  | .app _ _ fn args => esgcFree fn ∧ esgcFreeList args
  | .fn _ _ _ _ body => setGlobals body = emptyGlobalBag
  | .letrec _ _ _ bindings body => funGlobals bindings = emptyGlobalBag ∧ esgcFree body
termination_by exp => sizeOf exp

/-- Flapjack helper for the source's EVERY predicate on expression lists. -/
def esgcFreeList : List ClosLang.Exp → Prop
  | [] => True
  | e :: es => esgcFree e ∧ esgcFreeList es
termination_by es => sizeOf es
end

/-- The recursive function helper is the original mapped list traversal. -/
theorem funGlobals_eq_elist (fs : List (Nat × ClosLang.Exp)) :
    funGlobals fs = elistGlobals (fs.map Prod.snd) := by
  induction fs with
  | nil => simp [funGlobals, elistGlobals]
  | cons f fs ih =>
    obtain ⟨n, body⟩ := f
    simp [funGlobals, elistGlobals, ih]

/-- The structural helper is the source's EVERY over expressions. -/
theorem esgcFreeList_iff (xs : List ClosLang.Exp) :
    esgcFreeList xs ↔ ∀ e ∈ xs, esgcFree e := by
  induction xs with
  | nil => simp [esgcFreeList]
  | cons x xs ih => simp [esgcFreeList, ih]

end Flapjack.Compiler.Backend.ClosProps
