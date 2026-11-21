module

public import Flapjack.Compiler.Backend.ClosLang.Syntax
public import Flapjack.Compiler.Backend.FlatProps.Globals
public import Flapjack.Compiler.Backend.FlatProps.GlobalBagProperties

@[expose] public section

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

/-- Global-write bags distribute over concatenation of closure expressions. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "elist_globals_append"]
theorem elistGlobals_append (xs ys : List ClosLang.Exp) :
    elistGlobals (xs ++ ys) = unionGlobalBag (elistGlobals xs) (elistGlobals ys) := by
  induction xs with
  | nil => funext key; simp [elistGlobals, emptyGlobalBag, unionGlobalBag, Flapjack.emptyBag, Flapjack.bagUnion]
  | cons x xs ih =>
    simp only [List.cons_append, elistGlobals, ih]
    funext key
    simp [unionGlobalBag, Flapjack.bagUnion, Nat.add_assoc]

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


/-- An expression with no global writes is safe for closure capture. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "set_globals_empty_esgc_free"]
theorem setGlobalsEmptyEsgcFree (expression : ClosLang.Exp) :
    setGlobals expression = emptyGlobalBag → esgcFree expression := by
  induction expression using setGlobals.induct
    (motive2 := fun _ => True)
    (motive3 := fun es => elistGlobals es = emptyGlobalBag → esgcFreeList es) <;>
    simp_all [setGlobals, elistGlobals, esgcFree, esgcFreeList, FlatProps.unionGlobalBag_eq_empty]

/-- Global-bag union is commutative. Flapjack infrastructure for the reverse
lemma; HOL states this law in its bag theory rather than in this script. -/
private theorem unionGlobalBag_comm (left right : GlobalBag) :
    unionGlobalBag left right = unionGlobalBag right left := by
  funext key
  simp only [unionGlobalBag, Flapjack.bagUnion]
  omega

/-- An expression list has an empty global bag exactly when every member's
bag is empty. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "elglobals_EQ_EMPTY"]
theorem elistGlobals_eq_empty (l : List ClosLang.Exp) :
    elistGlobals l = emptyGlobalBag ↔ ∀ e ∈ l, setGlobals e = emptyGlobalBag := by
  induction l with
  | nil => simp [elistGlobals]
  | cons e es ih =>
    simp [elistGlobals, FlatProps.unionGlobalBag_eq_empty, ih]

/-- The expression-list bag is the source's right fold over the mapped
per-expression bags. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "elist_globals_FOLDR"]
theorem elistGlobals_foldr (es : List ClosLang.Exp) :
    elistGlobals es =
      List.foldr unionGlobalBag emptyGlobalBag (es.map setGlobals) := by
  induction es with
  | nil => simp [elistGlobals]
  | cons e es ih => simp [elistGlobals, ih]

/-- Reversing an expression list does not change its global bag. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "elist_globals_reverse"]
theorem elistGlobals_reverse (ls : List ClosLang.Exp) :
    elistGlobals ls.reverse = elistGlobals ls := by
  induction ls with
  | nil => simp [elistGlobals]
  | cons x xs ih =>
    rw [List.reverse_cons, elistGlobals_append, ih]
    simp only [elistGlobals, Flapjack.bagUnion_empty_right]
    exact (unionGlobalBag_comm (setGlobals x) (elistGlobals xs)).symm

end Flapjack.Compiler.Backend.ClosProps
