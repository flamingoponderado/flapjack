module

public import Flapjack.Compiler.Backend.SourceToFlat.ToClos
public import Flapjack.Compiler.Backend.ClosToBvl.Prepared
public import Flapjack.Compiler.Backend.BvlToBvi.Compile
public import Flapjack.Compiler.Backend.BvlToBvi.SourcePipeline

@[expose] public section

/-! Checked source-to-BVI compositions. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

/-- Compose the currently ported source, closure and BVL stages. The closure
configuration controls the closure passes; the bounded stages return `none`
on exhaustion. This omits the outer BVL/BVI optimization pipeline and does not establish final
compiler output parity or correctness. -/
def compileCakeToBviBeforeOptimizationsFuel (fuel : Nat) (source : Config)
    (closure : ClosToBvl.Config) (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × Nat × List (Nat × Nat × Bvi.Exp) × Nat × Spt Basis.Pure.MlString.MlString) := do
  let (source, exps) ← compileCakeToClosFuel fuel source decls
  let (closure, bvl, names) ← ClosToBvl.compileCallMtiFuel? fuel closure exps
  let (start, code, next) ← BvlToBvi.compileProgFuel fuel fuel closure.start 0 bvl
  let names := BvlToBvi.getNames (code.map fun (n, _, _) => n) names
  pure (source, closure, start, code, next, names)

/-- Run the BVL inlining pipeline before BVI lowering. Tail-recursion, TMC and
subsequent BVI optimizations remain separate. -/
def compileCakeToBviBvlOptimizedFuel (fuel inlineLimit cutSize : Nat) (splitSeq : Bool)
    (source : Config) (closure : ClosToBvl.Config) (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × Nat × List (Nat × Nat × Bvi.Exp) × Nat × Spt Basis.Pure.MlString.MlString) := do
  let (source, exps) ← compileCakeToClosFuel fuel source decls
  let (closure, bvl, names) ← ClosToBvl.compileCallMtiFuel? fuel closure exps
  let (_, bvl) ← BvlInline.compileProgFuel fuel inlineLimit cutSize splitSeq bvl
  let (start, code, next) ← BvlToBvi.compileProgFuel fuel fuel closure.start 0 bvl
  let names := BvlToBvi.getNames (code.map fun (n, _, _) => n) names
  pure (source, closure, start, code, next, names)

/-- Follow closure optimization and BVL inlining with BVI tail-recursion, TMC
and wrapper inlining, using explicit traversal fuel. -/
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

/-- Run the configured whole-program BVL/BVI pipeline, retaining its inline
maps and fresh-name counters for subsequent compiler invocations. -/
def compileCakeToBviConfiguredFuel (fuel : Nat) (source : Config) (closure : ClosToBvl.Config)
    (bvlConfig : BvlToBvi.Config) (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × BvlToBvi.Config × List (Nat × Nat × Bvi.Exp) × Spt Basis.Pure.MlString.MlString) := do
  let (source, exps) ← compileCakeToClosFuel fuel source decls
  let (closure, bvl, names) ← ClosToBvl.compileCallMtiFuel? fuel closure exps
  let (start, code, inlines, bviInlines, next1, next2, next3, names) :=
    BvlToBvi.compileSource closure.start bvlConfig names bvl
  let closure := { closure with start := start }
  let bvlConfig := { bvlConfig with inlines := inlines, bviInlines := bviInlines, nextName1 := next1, nextName2 := next2, nextName3 := next3 }
  pure (source, closure, bvlConfig, code, names)

/-- The checked closure route followed by BVI wrapper inlining and
tick removal. BVL inlining, tail-recursion and TMC passes remain absent. -/
def compileCakeToBviInlineFuel (fuel : Nat) (source : Config)
    (closure : ClosToBvl.Config) (decls : List AstHOL.Dec) :
    Option (Config × ClosToBvl.Config × Nat × List (Nat × Nat × Bvi.Exp) × Nat × Spt Basis.Pure.MlString.MlString) := do
  let (source, closure, start, code, next, names) ← compileCakeToBviBeforeOptimizationsFuel fuel source closure decls
  let (_, code) ← BviInline.compileProgFuel fuel code
  pure (source, closure, start, code, next, names)

end Flapjack.Compiler.Backend.SourceToFlat
