import Flapjack.Compiler.Backend.SourceToFlat.ToClos
import Flapjack.Compiler.Backend.ClosToBvl.Prepared
import Flapjack.Compiler.Backend.BvlToBvi.Compile

/-! Checked source-to-BVI composition with closure optimizations disabled. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

/-- Compose the currently ported source, closure and BVL stages. The closure
configuration must disable multi-argument introduction, known-function and
call optimizations; the bounded stages return `none` on exhaustion. This
omits the outer BVL/BVI optimization pipeline and does not establish final
compiler output parity or correctness. -/
def compileCakeToBviNoOptsFuel (fuel : Nat) (source : Config)
    (closure : ClosToBvl.Config) (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × Nat × List (Nat × Nat × Bvi.Exp) × Nat) := do
  let (source, exps) ← compileCakeToClosFuel fuel source decls
  let (closure, bvl, _) ← ClosToBvl.compileNoOpts? closure exps
  let (start, code, next) ← BvlToBvi.compileProgFuel fuel fuel closure.start 0 bvl
  pure (source, closure, start, code, next)

end Flapjack.Compiler.Backend.SourceToFlat
