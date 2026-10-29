import Flapjack.Compiler.Backend.FlatPattern.CompileTotal

/-! The current source pattern heuristic is not consulted by compilation. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.Basis.Pure.MlString

/-- Flapjack proof infrastructure showing that every component of the current
pattern compiler ignores its configuration. This explains why the original
semantics theorem can quantify its two configurations independently. -/
theorem compile_config_irrel (left right : Config) :
    (∀ e, compileExp left e = compileExp right e) ∧
    (∀ fs, compileFuns left fs = compileFuns right fs) ∧
    (∀ es, compileExps left es = compileExps right es) ∧
    (∀ ps, compileMatch left ps = compileMatch right ps) := by
  apply compileExp.mutual_induct left
  all_goals intros
  all_goals simp_all [compileExp, compileExps, compileMatch, compileFuns, compilePats]

/-- Changing the unused pattern configuration leaves compiled declarations
unchanged. This is Flapjack infrastructure, not a separate HOL theorem. -/
theorem compileDec_config_irrel (left right : Config) (e : FlatLang.Exp) :
    compileDec left e = compileDec right e := by
  simp only [compileDec, (compile_config_irrel left right).1 e]

end Flapjack.Compiler.Backend.FlatPattern
