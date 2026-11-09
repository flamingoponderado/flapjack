module

public import Flapjack.Compiler.Backend.SourceToFlat.Eliminate

@[expose] public section

/-! Source-to-flat allocation expressions survive flat elimination. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

/-- Global allocation is effectful and is always retained by elimination. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "keep_glob_alloc"]
theorem keepGlobAlloc {α : Type} (reachable : Spt α) (next : NextIndices) (config : Config) :
    FlatElim.keep reachable (globAlloc next config) = true := by
  simp [FlatElim.keep, globAlloc, FlatElim.isPure]

end Flapjack.Compiler.Backend.SourceToFlat
