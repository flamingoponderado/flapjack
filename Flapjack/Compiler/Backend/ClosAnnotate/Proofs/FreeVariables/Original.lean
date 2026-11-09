import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.FreeVariables
import Flapjack.Compiler.Backend.ClosAnnotate.Free.OriginalEquivalence

/-! Source-shaped free-variable observation for closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open ClosLang DbVars

/-- The source free-variable observation uses the original free-variable pass. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "alt_fv_def"]
noncomputable def altFvSource (index : Nat) (expressions : List Exp) : Bool :=
  hasVar index (altFreeSource expressions).2

/-- The optimized observation computes the source free-variable predicate. -/
theorem altFvSource_eq_altFv (index : Nat) (expressions : List Exp) :
    altFvSource index expressions = altFv index expressions := by
  simp [altFvSource, altFv, altFreeSource_eq_altFree]

end Flapjack.Compiler.Backend.ClosAnnotate
