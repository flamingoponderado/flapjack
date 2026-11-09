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

/-- Reuse the same closedness test as the known-closure pass. -/
@[hol "cakeml/compiler/backend/clos_callScript.sml" "closed_def"]
abbrev closed : ClosLang.Exp → Bool := ClosKnown.closedHOL

end Flapjack.Compiler.Backend.ClosCall
