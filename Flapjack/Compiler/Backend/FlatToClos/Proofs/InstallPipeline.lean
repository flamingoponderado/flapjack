import Flapjack.Compiler.Backend.FlatToClos.Proofs.StateRelation
import Flapjack.Compiler.Backend.ClosInterp.Proofs.StateRelation

/-! Composition of flat-to-closure compilation with interpreter insertion.
These identities connect the actual compiler callbacks; the semantic
correctness of interpreter insertion remains a separate proof obligation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.Compiler.Backend.BackendProps

/-- The executable callback factors through the unoptimized compiler and
interpreter insertion. -/
theorem incrementalCompiler_factor {C : Type} (compiler : ClosSem.Compiler C) :
    pureCc incCompileDecs compiler =
      pureCc incCompileDecsProofSide (pureCc ClosInterp.insertProgram compiler) := rfl

/-- Future executable programs factor through the same two transformations. -/
theorem incrementalOracle_factor {C : Type} (oracle : Nat → C × List FlatLang.Exp) :
    pureCo incCompileDecs ∘ oracle =
      pureCo ClosInterp.insertProgram ∘ pureCo incCompileDecsProofSide ∘ oracle := by
  funext index
  cases oracle index
  rfl

/-- A production callback relation supplies the intermediate callback
required by the flat-to-closure simulation. -/
theorem production_installConfigRel {C : Type} (source : FlatSem.InstallConfig C)
    (compiler : ClosSem.Compiler C)
    (safe : ∀ index, FlatProps.noMatDecs (source.compileOracle index).2 = true)
    (production : source.compile = pureCc incCompileDecs compiler) :
    installConfigRel source (pureCo (incCompileDecsProofSide (α := Nat × Nat × ClosLang.Exp)) ∘ source.compileOracle)
      (pureCc ClosInterp.insertProgram compiler) := by
  refine ⟨safe, rfl, ?_⟩
  simpa only [incrementalCompiler_factor] using production


end Flapjack.Compiler.Backend.FlatToClos
