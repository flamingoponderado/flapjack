module

public import Flapjack.Compiler.Backend.WordBignum.Compile
public import Flapjack.Compiler.Backend.WordBignum.Proofs.Equality

@[expose] public section

/-! The polymorphic source cache lookup and its executable specialization. -/
namespace Flapjack.Compiler.Backend.WordBignum

/-- HOL's first-match code lookup, with unrestricted key and code types.
The executable compiler uses `hasCompiled`; the theorem below connects it to
this source definition using the checked structural equality. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "has_compiled_def"]
noncomputable def hasCompiledHOL {α β : Type} (code : α) (cs : Nat × List (α × Nat × β)) : Sum Nat Nat := by
  classical
  exact hasCompiled code cs

/-- The executed cache operation agrees with the polymorphic HOL definition.
This is a representation-connection theorem, with no separate HOL name. -/
theorem hasCompiled_eq_HOL {α β : Type} [inst : DecidableEq α]
    (code : α) (cs : Nat × List (α × Nat × β)) :
    hasCompiled code cs = hasCompiledHOL code cs := by
  exact congrArg (fun d : DecidableEq α => @hasCompiled α β d code cs)
    (Subsingleton.elim inst (Classical.typeDecidableEq α))

end Flapjack.Compiler.Backend.WordBignum
