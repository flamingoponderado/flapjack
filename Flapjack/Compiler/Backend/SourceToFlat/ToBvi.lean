import Flapjack.Compiler.Backend.SourceToFlat.ToClos
import Flapjack.Compiler.Backend.ClosToBvl.Prepared
import Flapjack.Compiler.Backend.BvlToBvi.Compile
import Flapjack.Compiler.Backend.BvlToBvi.Names
import Flapjack.Compiler.Backend.BviInline
import Flapjack.Compiler.Backend.BvlInline
import Flapjack.Compiler.Backend.BviTailrec.Rewrite
import Flapjack.Compiler.Backend.BviTmc

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

/-- Multi-argument introduction followed by the implemented BVL inlining
and simplification stages. This deliberately omits `bvl_handle`, tail-call
optimizations and the remaining frontend optimizations. -/
def compileCakeToBviBvlInlineFuel (fuel limit : Nat) (source : Config)
    (closure : ClosToBvl.Config) (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × Nat × List (Nat × Nat × Bvi.Exp) × Nat × Spt Basis.Pure.MlString.MlString) := do
  let (source, exps) ← compileCakeToClosFuel fuel source decls
  let (closure, bvl, names) ← ClosToBvl.compileMtiOnlyFuel? fuel closure exps
  let (_, bvl) ← BvlInline.compileWithoutHandleFuel fuel limit bvl
  let (start, code, next) ← BvlToBvi.compileProgFuel fuel fuel closure.start 0 bvl
  let names := BvlToBvi.getNames (code.map fun (n, _, _) => n) names
  pure (source, closure, start, code, next, names)

/-- Continue BVL inlining through handler processing, with constant folding
and later BVL/BVI optimizations still omitted. -/
def compileCakeToBviBvlHandleFuel (fuel inlineLimit cutSize : Nat) (splitSeq : Bool)
    (source : Config) (closure : ClosToBvl.Config) (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × Nat × List (Nat × Nat × Bvi.Exp) × Nat × Spt Basis.Pure.MlString.MlString) := do
  let (source, exps) ← compileCakeToClosFuel fuel source decls
  let (closure, bvl, names) ← ClosToBvl.compileMtiOnlyFuel? fuel closure exps
  let (_, bvl) ← BvlInline.compileWithoutConstantsFuel fuel inlineLimit cutSize splitSeq bvl
  let (start, code, next) ← BvlToBvi.compileProgFuel fuel fuel closure.start 0 bvl
  let names := BvlToBvi.getNames (code.map fun (n, _, _) => n) names
  pure (source, closure, start, code, next, names)

/-- Run the BVL inlining pipeline before BVI lowering. Known-function,
call, tail-recursion, TMC and subsequent BVI optimizations remain separate. -/
def compileCakeToBviBvlOptimizedFuel (fuel inlineLimit cutSize : Nat) (splitSeq : Bool)
    (source : Config) (closure : ClosToBvl.Config) (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × Nat × List (Nat × Nat × Bvi.Exp) × Nat × Spt Basis.Pure.MlString.MlString) := do
  let (source, exps) ← compileCakeToClosFuel fuel source decls
  let (closure, bvl, names) ← ClosToBvl.compileMtiOnlyFuel? fuel closure exps
  let (_, bvl) ← BvlInline.compileProgFuel fuel inlineLimit cutSize splitSeq bvl
  let (start, code, next) ← BvlToBvi.compileProgFuel fuel fuel closure.start 0 bvl
  let names := BvlToBvi.getNames (code.map fun (n, _, _) => n) names
  pure (source, closure, start, code, next, names)

/-- Follow closure direct-call conversion and BVL inlining with BVI
tail-recursion, TMC and wrapper inlining. Known-function optimization remains
unsupported. -/
def compileCakeToBviOptimizedInlineFuel (fuel inlineLimit cutSize : Nat) (splitSeq : Bool)
    (source : Config) (closure : ClosToBvl.Config) (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × Nat × List (Nat × Nat × Bvi.Exp) × Nat × Spt Basis.Pure.MlString.MlString) := do
  let (source, exps) ← compileCakeToClosFuel fuel source decls
  let (closure, bvl, names) ← ClosToBvl.compileCallMtiFuel? fuel closure exps
  let (_, bvl) ← BvlInline.compileProgFuel fuel inlineLimit cutSize splitSeq bvl
  let (start, code, next) ← BvlToBvi.compileProgFuel fuel fuel closure.start 0 bvl
  let (_, code) ← BviTailrec.compileProgFuel fuel true (Flapjack.bvlNumStubs + 2) code
  let (_, code) ← BviTmc.compileProgFuel fuel true (Flapjack.bvlNumStubs + 3) code
  let (_, code) ← BviInline.compileProgFuel fuel code
  let names := BvlToBvi.getNames (code.map fun (n, _, _) => n) names
  pure (source, closure, start, code, next, names)

/-- Run BVL optimization, accept only BVI functions whose tail-recursion
analysis selects no rewrite, then apply BVI inlining. The tail-modulo-
constructor optimizer and positive tail-recursion rewrites are absent. -/
def compileCakeToBviTailrecCheckedFuel (fuel inlineLimit cutSize : Nat) (splitSeq : Bool)
    (source : Config) (closure : ClosToBvl.Config) (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × Nat × List (Nat × Nat × Bvi.Exp) × Nat × Spt Basis.Pure.MlString.MlString) := do
  let (source, closure, start, code, next, names) ←
    compileCakeToBviBvlOptimizedFuel fuel inlineLimit cutSize splitSeq source closure decls
  let (_, code) ← BviTailrec.compileNoRewriteFuel fuel true (Flapjack.bvlNumStubs + 2) code
  let (_, code) ← BviInline.compileProgFuel fuel code
  pure (source, closure, start, code, next, names)

/-- The checked multi-argument route followed by BVI wrapper inlining and
tick removal. BVL inlining, tail-recursion and TMC passes remain absent. -/
def compileCakeToBviInlineFuel (fuel : Nat) (source : Config)
    (closure : ClosToBvl.Config) (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × Nat × List (Nat × Nat × Bvi.Exp) × Nat × Spt Basis.Pure.MlString.MlString) := do
  let (source, closure, start, code, next, names) ← compileCakeToBviMtiFuel fuel source closure decls
  let (_, code) ← BviInline.compileProgFuel fuel code
  pure (source, closure, start, code, next, names)

end Flapjack.Compiler.Backend.SourceToFlat
