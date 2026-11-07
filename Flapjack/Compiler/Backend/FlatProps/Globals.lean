import Flapjack.Compiler.Backend.FlatLang

/-! Global-initialization bags and closure-freedom for flat expressions. -/
namespace Flapjack.Compiler.Backend.FlatProps

/-- HOL bags are functions from elements to natural-number multiplicities. -/
abbrev GlobalBag := Nat → Nat

/-- The empty global bag. -/
def emptyGlobalBag : GlobalBag := fun _ => 0

/-- Pointwise union of global bags. -/
def unionGlobalBag (left right : GlobalBag) : GlobalBag := fun key => left key + right key

/-- A global-initialization operator contributes its destination once. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "op_gbag_def"]
def opGlobalBag : FlatLang.Op → GlobalBag
  | .globalVarInit index => fun key => if key = index then 1 else 0
  | _ => emptyGlobalBag

mutual
/-- Global initializations in a flat expression, with their multiplicities. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "set_globals_def"]
def setGlobals : FlatLang.Exp → GlobalBag
  | .raise _ expression | .fn _ _ expression => setGlobals expression
  | .handle _ expression rows | .mat _ expression rows => unionGlobalBag (setGlobals expression) (rowGlobals rows)
  | .con _ _ expressions => elistGlobals expressions
  | .app _ op expressions => unionGlobalBag (elistGlobals expressions) (opGlobalBag op)
  | .if_ _ first second third => unionGlobalBag (unionGlobalBag (setGlobals first) (setGlobals second)) (setGlobals third)
  | .let_ _ _ first second => unionGlobalBag (setGlobals first) (setGlobals second)
  | .letrec _ funs body => unionGlobalBag (setGlobals body) (funGlobals funs)
  | _ => emptyGlobalBag
termination_by expression => sizeOf expression

/-- The list clauses of the original global-bag traversal. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "set_globals_def"]
def elistGlobals : List FlatLang.Exp → GlobalBag
  | [] => emptyGlobalBag
  | expression :: rest => unionGlobalBag (setGlobals expression) (elistGlobals rest)
termination_by expressions => sizeOf expressions

/-- Flapjack helper corresponding to traversing the second components of rows. -/
def rowGlobals : List (FlatLang.Pat × FlatLang.Exp) → GlobalBag
  | [] => emptyGlobalBag
  | (_, body) :: rest => unionGlobalBag (setGlobals body) (rowGlobals rest)
termination_by rows => sizeOf rows

/-- Flapjack helper corresponding to traversing recursive function bodies. -/
def funGlobals : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp) → GlobalBag
  | [] => emptyGlobalBag
  | (_, _, body) :: rest => unionGlobalBag (setGlobals body) (funGlobals rest)
termination_by funs => sizeOf funs
end

/-- Global-initialization bags of appended expression lists combine by union. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "elist_globals_append"]
theorem elistGlobals_append (xs ys : List FlatLang.Exp) :
    elistGlobals (xs ++ ys) = unionGlobalBag (elistGlobals xs) (elistGlobals ys) := by
  induction xs with
  | nil =>
    funext key
    simp [elistGlobals, emptyGlobalBag, unionGlobalBag]
  | cons x xs ih =>
    simp only [List.cons_append, elistGlobals, ih]
    funext key
    simp [unionGlobalBag, Nat.add_assoc]

/-- Flapjack helper: the row traversal equals HOL's mapped list traversal;
this equality is not a separate HOL declaration. -/
theorem rowGlobals_eq_elistGlobals (rows : List (FlatLang.Pat × FlatLang.Exp)) :
    rowGlobals rows = elistGlobals (rows.map Prod.snd) := by
  induction rows with
  | nil => simp [rowGlobals, elistGlobals]
  | cons row rest ih =>
    obtain ⟨pattern, body⟩ := row
    simp [rowGlobals, elistGlobals, ih]

/-- Flapjack helper: the function traversal equals HOL's mapped list traversal;
this equality is not a separate HOL declaration. -/
theorem funGlobals_eq_elistGlobals
    (funs : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp)) :
    funGlobals funs = elistGlobals (funs.map (fun (_, _, body) => body)) := by
  induction funs with
  | nil => simp [funGlobals, elistGlobals]
  | cons fn rest ih =>
    obtain ⟨name, arg, body⟩ := fn
    simp [funGlobals, elistGlobals, ih]

mutual
/-- No function body captures a global initialization. The expression
carriers remain pending HOL correspondence review. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "esgc_free_def" 836]
def esgcFree : FlatLang.Exp → Prop
  | .raise _ expression => esgcFree expression
  | .handle _ expression rows | .mat _ expression rows => esgcFree expression ∧ esgcFreeRows rows
  | .con _ _ expressions | .app _ _ expressions => esgcFreeList expressions
  | .fn _ _ body => setGlobals body = emptyGlobalBag
  | .if_ _ first second third => esgcFree first ∧ esgcFree second ∧ esgcFree third
  | .let_ _ _ first second => esgcFree first ∧ esgcFree second
  | .letrec _ funs body => esgcFree body ∧ funGlobals funs = emptyGlobalBag
  | _ => True
termination_by expression => sizeOf expression

/-- Flapjack list traversal for the original EVERY predicate. -/
def esgcFreeList : List FlatLang.Exp → Prop
  | [] => True
  | expression :: rest => esgcFree expression ∧ esgcFreeList rest
termination_by expressions => sizeOf expressions

/-- Flapjack row traversal for the original EVERY over row bodies. -/
def esgcFreeRows : List (FlatLang.Pat × FlatLang.Exp) → Prop
  | [] => True
  | (_, body) :: rest => esgcFree body ∧ esgcFreeRows rest
termination_by rows => sizeOf rows
end

/-- The list traversal renders HOL's EVERY predicate over global-safety checks. -/
theorem esgcFreeList_iff (xs : List FlatLang.Exp) :
    esgcFreeList xs ↔ ∀ x ∈ xs, esgcFree x := by
  induction xs with
  | nil => simp [esgcFreeList]
  | cons x xs ih => simp [esgcFreeList, ih]

end Flapjack.Compiler.Backend.FlatProps
