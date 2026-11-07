import Flapjack.Compiler.Backend.ClosLang.Syntax

/-! Detect runtime installation in closure-language expressions. -/
namespace Flapjack.Compiler.Backend.ClosLang

mutual
/-- Detect `Install` throughout an expression, including nested functions. -/
@[hol "cakeml/compiler/backend/closLangScript.sml" "has_install_def"]
def hasInstall : Exp → Bool
  | .var _ _ => false
  | .ifThenElse _ a b c => hasInstall a || hasInstall b || hasInstall c
  | .let _ es e => hasInstall e || hasInstallList es
  | .op _ .install _ => true
  | .op _ _ es => hasInstallList es
  | .raise _ e | .tick _ e | .fn _ _ _ _ e => hasInstall e
  | .handle _ a b => hasInstall a || hasInstall b
  | .call _ _ _ es => hasInstallList es
  | .app _ _ e es => hasInstall e || hasInstallList es
  | .letrec _ _ _ fs e => hasInstallFuns fs || hasInstall e

/-- List clauses of the installation analysis. -/
@[hol "cakeml/compiler/backend/closLangScript.sml" "has_install_def"]
def hasInstallList : List Exp → Bool
  | [] => false
  | e :: es => hasInstall e || hasInstallList es

/-- Traverse recursive function bodies in order. -/
def hasInstallFuns : List (Nat × Exp) → Bool
  | [] => false
  | (_, e) :: fs => hasInstall e || hasInstallFuns fs
end

end Flapjack.Compiler.Backend.ClosLang
