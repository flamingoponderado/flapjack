module

public import Flapjack.Compiler.Backend.Semantics.ClosProps.FnAnnotations
public import Flapjack.Compiler.Backend.Semantics.ClosProps.CodeLocations

@[expose] public section

/-! Source syntax condition for closure-call correctness. -/
namespace Flapjack.Compiler.Backend.ClosCall
open ClosProps

/-- Closure-call source syntax requires function locations, absent
free-variable annotations, and distinct code locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "syntax_ok_def"]
def syntaxOk (expressions : List ClosLang.Exp) : Prop :=
  everyFnLocationSome expressions ∧ everyFnVarsNone expressions ∧ (codeLocations expressions).Nodup

end Flapjack.Compiler.Backend.ClosCall
