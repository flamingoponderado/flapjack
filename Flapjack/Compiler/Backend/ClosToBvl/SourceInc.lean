import Flapjack.Compiler.Backend.ClosToBvl.SourceExps
import Flapjack.Compiler.Backend.ClosToBvl.ExtractName

/-! Source-shaped incremental closure-to-BVL compilation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Extract the entry location, chain the expressions, and compile the resulting
program. The entry extraction uses the executable pattern match; HOL's original
choice-based extraction and its equivalence remain to be ported. -/
noncomputable def compileInc (maxApp : Nat) (program : List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)) :
    List (Nat × Nat × Bvl.Exp) :=
  let (start, expressions) := extractName program.1
  compileProgExpsHOL maxApp (chainExps start expressions ++ program.2)

end Flapjack.Compiler.Backend.ClosToBvl
