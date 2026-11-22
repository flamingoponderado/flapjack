module

public import Flapjack.Compiler.Backend.ClosKnown.Inline.Free

@[expose] public section

/-! The direct-call and known-closure passes share the same free traversal. -/
namespace Flapjack.Compiler.Backend.ClosCall

/-- Reuse the shared traversal: the two CakeML scripts define the same
free-variable analysis on closure expressions. -/
@[hol "cakeml/compiler/backend/clos_callScript.sml" "free_def"]
abbrev free : List ClosLang.Exp → List ClosLang.Exp × DbVars.DbVarSet :=
  ClosKnown.freeHOL

/-- The single-expression traversal. HOL's `free_sing_def` declares this
function together with the auxiliary `free_list`; its clauses agree
clause-for-clause with the shared `ClosKnown.freeExpHOL` traversal. -/
@[hol "cakeml/compiler/backend/clos_callScript.sml" "free_sing_def"]
abbrev freeSing : ClosLang.Exp → ClosLang.Exp × DbVars.DbVarSet :=
  ClosKnown.freeExpHOL

/-- The auxiliary list traversal declared by the same `free_sing_def`. Its
empty/cons clauses are exactly the shared `ClosKnown.freeHOL` recursion that
`free` abbreviates, so `free_sing_eq`'s second conjunct is definitional. -/
@[hol "cakeml/compiler/backend/clos_callScript.sml" "free_sing_def"]
abbrev freeList : List ClosLang.Exp → List ClosLang.Exp × DbVars.DbVarSet :=
  ClosKnown.freeHOL

/-- Reuse the same closedness test as the known-closure pass. -/
@[hol "cakeml/compiler/backend/clos_callScript.sml" "closed_def"]
abbrev closed : ClosLang.Exp → Bool := ClosKnown.closedHOL

end Flapjack.Compiler.Backend.ClosCall
