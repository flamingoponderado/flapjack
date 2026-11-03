import Flapjack.Compiler.Backend.ClosToBvl.Proofs.KnownPipelineSemantics
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.AnnotatedPrepared

/-! Composition of known-function optimization and prepared BVL compilation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.ClosKnown

/-- The future closure program after numbering and the known-function,
free-variable, tick and let-operation passes. -/
noncomputable abbrev knownClosureFuture {C : Type} (knownConfig : ClosKnown.Config)
    (oracle : CompileOracle (Nat × (Spt ValApprox × C))) : CompileOracle C :=
  pureCo letopInc ∘ pureCo ticksInc ∘ stateCo (ClosKnown.compileInc knownConfig)
    (pureCo fvsInc ∘ stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)

/-- The known-function closure pipeline and prepared BVL conversion preserve
observations when their existing syntax, label-boundary and compilation
invariants hold. This is Lean-side pass composition, not a HOL declaration;
the location and oracle boundary premises still need to be derived from the
complete compiler driver. -/
theorem known_pipeline_prepared_semantics {C F : Type} (ffi : HolFfiState F)
    (fuel maxApp number start : Nat) (knownConfig : ClosKnown.Config)
    (oracle : CompileOracle (Nat × (Spt ValApprox × C))) (targetCompiler : BvlSem.Compiler C)
    (program : List ClosLang.Exp) (optimized : List (ClosLang.Exp × ValApprox))
    (globals : Spt ValApprox) (optimizedOutput : List ClosLang.Exp)
    (original current output : Config) (compiled : List (Nat × Nat × Bvl.Exp))
    (names : Spt Flapjack.Basis.Pure.MlString.MlString) (boundary : Nat → Nat)
    (positive : 1 ≤ maxApp)
    (nonfail : semantics ffi maxApp HolFiniteMapExact.holEmpty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (pureCc fvsInc (stateCc (ClosKnown.compileInc knownConfig)
          (pureCc ticksInc (pureCc letopInc
            (pureCc ClosAnnotate.compileInc (pureCc (compileInc maxApp) targetCompiler))))))) program ≠ .fail)
    (numberSafe : ¬ containsAppSome maxApp program ∧
      ∀ n, (oracle n).2.2 = [] ∧ ¬ containsAppSome maxApp (oracle n).2.1)
    (knownSafe :
      let numberedCo := stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle
      let xs := (ClosNumber.renumberList number program).2
      syntaxOracleOk knownConfig xs numberedCo globals ∧
      ClosKnown.knownListTotal knownConfig (ClosFvs.compile xs) [] .ln = (optimized, globals))
    (optRun : ((optimized.map Prod.fst).mapM fun e => do
      let e ← ClosTicks.removeBounded fuel e
      ClosLetop.compileBounded fuel e) = some optimizedOutput)
    (startEq : current.start = start) (maxAppEq : current.maxApp = maxApp)
    (compile : compilePrepared? original current program (ClosAnnotate.compile (chainExps start optimizedOutput)) =
      some (output, compiled, names))
    (distinct : (compiled.map Prod.fst).Nodup)
    (optimizedLocations : everyFnLocationSome (optimized.map Prod.fst))
    (monotone : ∀ {i j}, i ≤ j → boundary i ≤ boundary j)
    (initialBelow : ∀ location ∈ compiled.map Prod.fst, location < boundary 0)
    (futureDistinct : ∀ i, ((compileInc maxApp
      (ClosAnnotate.compileInc (knownClosureFuture knownConfig oracle i).2)).map Prod.fst).Nodup)
    (ranges : ∀ i location, location ∈ (compileInc maxApp
      (ClosAnnotate.compileInc (knownClosureFuture knownConfig oracle i).2)).map Prod.fst →
      boundary i ≤ location ∧ location < boundary (i + 1))
    (knownFutureLocations : ∀ i, everyFnLocationSome
      (stateCo (ClosKnown.compileInc knownConfig)
        (pureCo fvsInc ∘ stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) i).2.1) :
    BvlSem.semantics ffi (sptFromAList compiled)
      (pureCo (compileInc maxApp) ∘ pureCo ClosAnnotate.compileInc ∘ knownClosureFuture knownConfig oracle)
      targetCompiler output.start =
    semantics ffi maxApp HolFiniteMapExact.holEmpty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (pureCc fvsInc (stateCc (ClosKnown.compileInc knownConfig)
          (pureCc ticksInc (pureCc letopInc
            (pureCc ClosAnnotate.compileInc (pureCc (compileInc maxApp) targetCompiler))))))) program := by
  obtain ⟨_, output', _, outputRun, _, _, chainEq⟩ :=
    number_fvs_known_ticks_letop_annotate_semantics ffi fuel maxApp number start knownConfig oracle
      (pureCc (compileInc maxApp) targetCompiler) program optimized globals positive nonfail numberSafe knownSafe
  have same : output' = optimizedOutput := Option.some.inj (outputRun.symm.trans optRun)
  subst output'
  have chainNonfail : semantics ffi current.maxApp
      (initialSourceCode (ClosAnnotate.compile (chainExps start optimizedOutput)))
      (pureCo ClosAnnotate.compileInc ∘ knownClosureFuture knownConfig oracle)
      (pureCc (compileInc current.maxApp) targetCompiler) [.call .none 0 current.start []] ≠ .fail := by
    simpa [maxAppEq, startEq, knownClosureFuture] using chainEq ▸ nonfail
  have outputLocations : everyFnLocationSome optimizedOutput := by
    have outputEq := Option.some.inj ((ticks_letop_bounded fuel (optimized.map Prod.fst)).symm.trans optRun)
    rw [← outputEq]
    exact (ClosLetop.compileList_locations _).mpr ((ClosTicks.removeList_locations _).mpr optimizedLocations)
  have locations : ∀ name arity body, (name, arity, body) ∈ chainExps start optimizedOutput →
      everyFnLocationSome [body] := by
    have chain := (chainExps_annotations start optimizedOutput).1.mpr outputLocations
    intro name arity body member
    apply ClosNumber.locations_member _ body chain
    exact List.mem_map.mpr ⟨(name, arity, body), member, rfl⟩
  have futureLocations : ∀ i, everyFnLocationSome (knownClosureFuture knownConfig oracle i).2.1 ∧
      ∀ entry ∈ (knownClosureFuture knownConfig oracle i).2.2, everyFnLocationSome [entry.2.2] := by
    intro i
    constructor
    · simpa [knownClosureFuture, pureCo, letopInc, ticksInc, ClosLetop.compileInc, ClosTicks.compileInc] using
        (ClosLetop.compileList_locations _).mpr ((ClosTicks.removeList_locations _).mpr (knownFutureLocations i))
    · simp [knownClosureFuture, pureCo, letopInc, ClosLetop.compileInc]
  have compiledEq := compilePrepared_annotated_semantics ffi original current output program
    (chainExps start optimizedOutput) compiled names (knownClosureFuture knownConfig oracle)
    targetCompiler boundary compile chainNonfail distinct locations monotone initialBelow
    (by simpa [maxAppEq] using futureDistinct) (by simpa [maxAppEq] using ranges) futureLocations
  apply Eq.trans ?_ chainEq
  simpa [maxAppEq, startEq, knownClosureFuture] using compiledEq

end Flapjack.Compiler.Backend.ClosToBvl
