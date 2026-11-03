import Flapjack.Compiler.Backend.ClosLang.HasInstall

/-! Source-equation support for the factored installation traversal. -/
namespace Flapjack.Compiler.Backend.ClosLang

/-- The recursive-function helper is HOL's installation test on the mapped
function bodies. This is Lean infrastructure for the original mutual clauses. -/
theorem hasInstallFuns_eq_map (functions : List (Nat × Exp)) :
    hasInstallFuns functions = hasInstallList (functions.map Prod.snd) := by
  induction functions with
  | nil => rfl
  | cons entry rest ih =>
    cases entry
    simp [hasInstallFuns, hasInstallList, ih]

end Flapjack.Compiler.Backend.ClosLang
