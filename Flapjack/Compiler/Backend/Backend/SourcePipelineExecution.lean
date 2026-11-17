module

public import Flapjack.Compiler.Backend.Backend.SourcePipeline
public import Flapjack.Compiler.Backend.SourceToFlat.ToRiscV
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.WholeProgram

@[expose] public section

-- The existing `Backend.Backend` namespace mirrors the HOL backend theory.
set_option linter.dupNamespace false

/-! Connecting the source-shaped pipeline to the executable frontend. -/
namespace Flapjack.Compiler.Backend.Backend

/-- The configured executable BVI pipeline returns the source pipeline's
    updated configurations and program. The executable adds stub names in
    its next stage, so this comparison applies that same operation here.
    This is Flapjack-specific correspondence infrastructure. -/
theorem toBvi_executable (fuel : Nat) (c : Config) (p : List AstHOL.Dec) :
    (SourceToFlat.compileCakeToBviConfiguredFuel fuel c.sourceConf c.closConf c.bvlConf p).map
      (fun (source, clos, bvl, program, names) =>
        ({ c with sourceConf := source, closConf := clos, bvlConf := bvl },
          program, SourceToFlat.backendNames names)) = some (toBvi c p) := by
  simp [SourceToFlat.compileCakeToBviConfiguredFuel, SourceToFlat.compileCakeToClosFuel,
    SourceToFlat.compileToClosFuel, ClosToBvl.compileCallMtiFuel_eq_source,
    toBvi, toBvl, toClos, toFlat, SourceToFlat.backendNames]

end Flapjack.Compiler.Backend.Backend
