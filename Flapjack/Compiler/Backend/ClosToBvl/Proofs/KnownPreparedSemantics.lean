import Flapjack.Compiler.Backend.ClosToBvl.Proofs.KnownPipelineSemantics
import Flapjack.Compiler.Backend.ClosKnown.Proofs.TraversalLocationsTotal
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.KnownInitialLabels
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.AnnotatedPrepared

/-! Composition of known-function optimization and prepared BVL compilation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.ClosKnown

/-- The known-function closure pipeline and prepared BVL conversion preserve
observations when their existing syntax, label-boundary and compilation
invariants hold. This is Lean-side pass composition, not a HOL declaration;
the numbering reservation, initial oracle bound, and source-run premises still
need to be derived from the complete compiler driver. -/
theorem known_pipeline_prepared_semantics {C F : Type} (ffi : HolFfiState F)
    (fuel maxApp number start : Nat) (knownConfig : ClosKnown.Config)
    (oracle : CompileOracle (Nat × (Spt ValApprox × C))) (targetCompiler : BvlSem.Compiler C)
    (program : List ClosLang.Exp) (optimized : List (ClosLang.Exp × ValApprox))
    (globals : Spt ValApprox) (optimizedOutput : List ClosLang.Exp)
    (original current output : Config) (compiled : List (Nat × Nat × Bvl.Exp))
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
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
    (numberLower : start + max 1 program.length ≤ number)
    (oracleState : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
    (initialBound : (ClosNumber.renumberList number program).1 ≤ (oracle 0).1.1)
    :
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
  have numberedLocations : ∀ i, everyFnLocationSome
      (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle i).2.1 := by
    intro i
    simpa [stateCo, ClosNumber.ignoreTable] using
      ClosNumber.compileInc_locations (oracle i).1.1 (oracle i).2.1
  have knownLocations := ClosKnown.TraversalLocations.syntaxOracleOk_outputLocations knownConfig
    (ClosNumber.renumberList number program).2
    (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) globals optimized knownSafe.1
    (ClosNumber.renumberList_locations program number) numberedLocations knownSafe.2
  have optimizedLocations := knownLocations.1
  have knownFutureLocations := knownLocations.2
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
  have outputLabels := numberedKnown_output_labels fuel number knownConfig program optimized globals optimizedOutput
    knownSafe.2 optRun
  have numberingBound := ClosNumber.renumberList_start_le program number
  have entryBound : start + max 1 optimizedOutput.length ≤ (ClosNumber.renumberList number program).1 := by
    rw [outputLabels.1]
    exact Nat.le_trans numberLower numberingBound
  have initialLabels := preparedChain_label_properties original current output program start
    (ClosNumber.renumberList number program).1 optimizedOutput compiled names compile outputLabels.2.1
    (by intro location member; have b := outputLabels.2.2 location member; omega) entryBound
  have distinct := initialLabels.1
  have initialBelow : ∀ location ∈ compiled.map Prod.fst, location < (oracle 0).1.1 + numStubs maxApp := by
    intro location member
    have bound := initialLabels.2 location member
    rw [maxAppEq] at bound
    omega
  let boundary := fun i => (oracle i).1.1 + numStubs maxApp
  have monotone : ∀ {i j}, i ≤ j → boundary i ≤ boundary j := by
    intro i j order
    exact Nat.add_le_add_right (numberingOracle_state_monotone oracle oracleState order) _
  have labels := knownClosureFuture_labels maxApp knownConfig oracle oracleState
  have futureDistinct := fun i => (labels i).1
  have ranges := fun i => (labels i).2
  have compiledEq := compilePrepared_annotated_semantics ffi original current output program
    (chainExps start optimizedOutput) compiled names (knownClosureFuture knownConfig oracle)
    targetCompiler boundary compile chainNonfail distinct locations monotone (by simpa [boundary] using initialBelow)
    (by simpa [maxAppEq] using futureDistinct) (by simpa [maxAppEq] using ranges) futureLocations
  apply Eq.trans ?_ chainEq
  simpa [maxAppEq, startEq, knownClosureFuture] using compiledEq

end Flapjack.Compiler.Backend.ClosToBvl
