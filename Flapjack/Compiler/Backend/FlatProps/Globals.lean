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
/-- Global initializations in a flat expression, with their multiplicities.
The expression carriers remain pending HOL correspondence review. -/
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

end Flapjack.Compiler.Backend.FlatProps
