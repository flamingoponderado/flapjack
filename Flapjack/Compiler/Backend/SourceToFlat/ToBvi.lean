import Flapjack.Compiler.Backend.SourceToFlat.ToClos
import Flapjack.Compiler.Backend.ClosToBvl.Prepared
import Flapjack.Compiler.Backend.BvlToBvi.Compile
import Flapjack.Compiler.Backend.BvlToBvi.Names

/-! Checked source-to-BVI composition with closure optimizations disabled. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

/-- Compose the currently ported source, closure and BVL stages. The closure
configuration must disable multi-argument introduction, known-function and
call optimizations; the bounded stages return `none` on exhaustion. This
omits the outer BVL/BVI optimization pipeline and does not establish final
compiler output parity or correctness. -/
def compileCakeToBviWithNamesNoOptsFuel (fuel : Nat) (source : Config)
    (closure : ClosToBvl.Config) (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × Nat × List (Nat × Nat × Bvi.Exp) × Nat × Spt Basis.Pure.MlString.MlString) := do
  let (source, exps) ← compileCakeToClosFuel fuel source decls
  let (closure, bvl, names) ← ClosToBvl.compileNoOpts? closure exps
  let (start, code, next) ← BvlToBvi.compileProgFuel fuel fuel closure.start 0 bvl
  let names := BvlToBvi.getNames (code.map fun (n, _, _) => n) names
  pure (source, closure, start, code, next, names)

/-- The restricted source-to-BVI composition without its symbol-name result. -/
def compileCakeToBviNoOptsFuel (fuel : Nat) (source : Config)
    (closure : ClosToBvl.Config) (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × Nat × List (Nat × Nat × Bvi.Exp) × Nat) := do
  let (source, closure, start, code, next, _) ← compileCakeToBviWithNamesNoOptsFuel fuel source closure decls
  pure (source, closure, start, code, next)

/-- Checked source-to-BVI composition allowing multi-argument introduction.
Known-function and call optimizations and the outer BVL/BVI optimizations
remain unsupported. -/
def compileCakeToBviMtiFuel (fuel : Nat) (source : Config)
    (closure : ClosToBvl.Config) (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × Nat × List (Nat × Nat × Bvi.Exp) × Nat × Spt Basis.Pure.MlString.MlString) := do
  let (source, exps) ← compileCakeToClosFuel fuel source decls
  let (closure, bvl, names) ← ClosToBvl.compileMtiOnlyFuel? fuel closure exps
  let (start, code, next) ← BvlToBvi.compileProgFuel fuel fuel closure.start 0 bvl
  let names := BvlToBvi.getNames (code.map fun (n, _, _) => n) names
  pure (source, closure, start, code, next, names)

end Flapjack.Compiler.Backend.SourceToFlat
