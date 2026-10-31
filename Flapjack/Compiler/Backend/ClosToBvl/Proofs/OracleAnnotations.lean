import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Oracle
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.AnnotationInvariants

/-! Annotation properties of the source oracle passed to closure-to-BVL. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.Compiler.Backend.BackendProps

/-- Incrementally annotating the source oracle supplies all variable
annotations and preserves each input function location. -/
theorem annotatedOracle_annotations {C : Type} (sourceOracle : ClosSem.CompileOracle C)
    (locations : ∀ index, ClosProps.everyFnLocationSome (sourceOracle index).2.1 ∧
      ∀ entry ∈ (sourceOracle index).2.2, ClosProps.everyFnLocationSome [entry.2.2]) :
    ∀ index,
      let program := ((pureCo ClosAnnotate.compileInc ∘ sourceOracle) index).2
      ClosProps.everyFnLocationSome program.1 ∧ ClosProps.everyFnVarsSome program.1 ∧
        (∀ entry ∈ program.2, ClosProps.everyFnLocationSome [entry.2.2]) ∧
        (∀ entry ∈ program.2, ClosProps.everyFnVarsSome [entry.2.2]) := by
  intro index
  have sourceLocations := locations index
  have preserved := ClosAnnotate.compileInc_locations (sourceOracle index).2 sourceLocations.1 sourceLocations.2
  have annotated := ClosAnnotate.compileInc_varsSome (sourceOracle index).2
  exact ⟨preserved.1, annotated.1, preserved.2, annotated.2⟩

/-- Construct the candidate oracle invariant for a source oracle transformed
by closure annotation, given ordered target-label intervals and source
location annotations. -/
theorem compileOracleInv_of_annotated_boundaries {C : Type} (maxApp : Nat)
    (sourceCode : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (sourceOracle : ClosSem.CompileOracle C) (targetCode : Spt (Nat × Bvl.Exp))
    (targetCompiler : BvlSem.Compiler C) (boundary : Nat → Nat)
    (monotone : ∀ {i j}, i ≤ j → boundary i ≤ boundary j)
    (initialBelow : ∀ location, sptMem location targetCode → location < boundary 0)
    (distinct : ∀ index, ((compileInc maxApp (ClosAnnotate.compileInc (sourceOracle index).2)).map Prod.fst).Nodup)
    (ranges : ∀ index location, location ∈ (compileInc maxApp (ClosAnnotate.compileInc (sourceOracle index).2)).map Prod.fst →
      boundary index ≤ location ∧ location < boundary (index + 1))
    (locations : ∀ index, ClosProps.everyFnLocationSome (sourceOracle index).2.1 ∧
      ∀ entry ∈ (sourceOracle index).2.2, ClosProps.everyFnLocationSome [entry.2.2]) :
    compileOracleInv maxApp sourceCode (pureCc (compileInc maxApp) targetCompiler)
      (pureCo ClosAnnotate.compileInc ∘ sourceOracle) targetCode targetCompiler
      (pureCo (compileInc maxApp) ∘ pureCo ClosAnnotate.compileInc ∘ sourceOracle) := by
  apply compileOracleInv_of_boundaries maxApp sourceCode (pureCo ClosAnnotate.compileInc ∘ sourceOracle)
    targetCode targetCompiler boundary monotone initialBelow
  · simpa [Function.comp_def, pureCo] using distinct
  · simpa [Function.comp_def, pureCo] using ranges
  · exact annotatedOracle_annotations sourceOracle locations

end Flapjack.Compiler.Backend.ClosToBvl
