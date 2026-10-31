import Flapjack.Compiler.Backend.ClosToBvl.Proofs.StubCode
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.OracleAnnotations

/-! Prepared compiler correctness with executable closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.Compiler.Backend.BackendProps

/-- The prepared compiler preserves proof-side behavior for an annotated
program and annotated future oracle. Variable annotations are supplied by
the annotation pass; input location annotations and label ordering remain
explicit prerequisites. -/
theorem compilePrepared_annotated_semantics {C F : Type} (ffi : HolFfiState F)
    (original current output : Config) (expressions : List ClosLang.Exp)
    (rawProgram : List (Nat × Nat × ClosLang.Exp)) (compiled : List (Nat × Nat × Bvl.Exp))
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (rawOracle : ClosSem.CompileOracle C) (targetCompiler : BvlSem.Compiler C) (boundary : Nat → Nat)
    (compile : compilePrepared? original current expressions (ClosAnnotate.compile rawProgram) =
      some (output, compiled, names))
    (nonfail : ClosSem.semantics ffi current.maxApp (initialSourceCode (ClosAnnotate.compile rawProgram))
      (pureCo ClosAnnotate.compileInc ∘ rawOracle) (pureCc (compileInc current.maxApp) targetCompiler)
      [.call .none 0 current.start []] ≠ .fail)
    (distinct : (compiled.map Prod.fst).Nodup)
    (programLocations : ∀ name arity body, (name, arity, body) ∈ rawProgram → ClosProps.everyFnLocationSome [body])
    (monotone : ∀ {i j}, i ≤ j → boundary i ≤ boundary j)
    (initialBelow : ∀ location ∈ compiled.map Prod.fst, location < boundary 0)
    (futureDistinct : ∀ index, ((compileInc current.maxApp (ClosAnnotate.compileInc (rawOracle index).2)).map Prod.fst).Nodup)
    (ranges : ∀ index location, location ∈ (compileInc current.maxApp (ClosAnnotate.compileInc (rawOracle index).2)).map Prod.fst →
      boundary index ≤ location ∧ location < boundary (index + 1))
    (futureLocations : ∀ index, ClosProps.everyFnLocationSome (rawOracle index).2.1 ∧
      ∀ entry ∈ (rawOracle index).2.2, ClosProps.everyFnLocationSome [entry.2.2]) :
    BvlSem.semantics ffi (sptFromAList compiled)
        (pureCo (compileInc current.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘ rawOracle) targetCompiler output.start =
      ClosSem.semantics ffi current.maxApp (initialSourceCode (ClosAnnotate.compile rawProgram))
        (pureCo ClosAnnotate.compileInc ∘ rawOracle) (pureCc (compileInc current.maxApp) targetCompiler)
        [.call .none 0 current.start []] := by
  apply compilePrepared_tree_semantics ffi original current output expressions (ClosAnnotate.compile rawProgram)
    compiled names (pureCo ClosAnnotate.compileInc ∘ rawOracle) (pureCc (compileInc current.maxApp) targetCompiler)
    (pureCo (compileInc current.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘ rawOracle)
    targetCompiler compile nonfail distinct
  · exact ClosAnnotate.compile_locations rawProgram programLocations
  · exact ClosAnnotate.compile_varsSome rawProgram
  · apply compileOracleInv_of_annotated_boundaries current.maxApp (initialSourceCode (ClosAnnotate.compile rawProgram))
      rawOracle (sptFromAList compiled) targetCompiler boundary monotone
      (fun location member => initialBelow location (emitted_tree_location_mem compiled location member))
      futureDistinct ranges futureLocations

end Flapjack.Compiler.Backend.ClosToBvl
