import Flapjack.Compiler.Backend.SourceToFlat.Eliminate

/-! Source-to-flat allocation expressions survive flat elimination. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

/-- Global allocation is effectful and is always retained by elimination. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "keep_glob_alloc"]
theorem keepGlobAlloc {α : Type} (reachable : Spt α) (next : NextIndices) (config : Config) :
    FlatElim.keep reachable (globAlloc next config) = true := by
  simp [FlatElim.keep, globAlloc, FlatElim.isPure]

/-- The compiler's reserved environment-reference initialization is effectful
and therefore retained. This is a Flapjack helper without a HOL declaration. -/
theorem keepAllocEnvRef {α : Type} (reachable : Spt α) : FlatElim.keep reachable allocEnvRef = true := by
  simp [FlatElim.keep, allocEnvRef, FlatElim.isPure, FlatElim.allPure]

/-- Elimination cannot remove the initial global allocation. This helper
follows from the allocation and filter definitions, without a HOL declaration. -/
theorem removeFlatProgTotal_globAlloc (next : NextIndices) (config : Config) (code : List FlatLang.Exp) :
    ∃ rest, FlatElim.removeFlatProgTotal (globAlloc next config :: code) = globAlloc next config :: rest := by
  unfold FlatElim.removeFlatProgTotal
  split
  · exact ⟨code, rfl⟩
  · cases FlatElim.analyseCode (globAlloc next config :: code) with
    | mk roots tree =>
      refine ⟨FlatElim.removeUnreachable (FlatElim.closureTotal roots tree) code, ?_⟩
      simp [FlatElim.removeUnreachable, keepGlobAlloc]

/-- Both source-to-flat initialization expressions survive elimination in
their original order. This is a Flapjack consequence of the two keep facts. -/
theorem removeFlatProgTotal_initialPrefix (next : NextIndices) (config : Config) (code : List FlatLang.Exp) :
    ∃ rest, FlatElim.removeFlatProgTotal (globAlloc next config :: allocEnvRef :: code) =
      globAlloc next config :: allocEnvRef :: rest := by
  unfold FlatElim.removeFlatProgTotal
  split
  · exact ⟨code, rfl⟩
  · cases FlatElim.analyseCode (globAlloc next config :: allocEnvRef :: code) with
    | mk roots tree =>
      refine ⟨FlatElim.removeUnreachable (FlatElim.closureTotal roots tree) code, ?_⟩
      simp [FlatElim.removeUnreachable, keepGlobAlloc, keepAllocEnvRef]

end Flapjack.Compiler.Backend.SourceToFlat
