import Flapjack.Compiler.Backend.ClosToBvl.Proofs.KnownCallLabels
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.KnownPreparedSemantics

/-! Semantics at the known-function to direct-call boundary. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.ClosKnown

/-- Numbering, free-variable cleanup, known-function optimization, tick
removal, and let-operation cleanup preserve observations up to the
direct-call pass. This is Lean-side composition, not a HOL theorem port. -/
theorem known_beforeCall_semantics {C F : Type} (ffi : HolFfiState F)
    (fuel maxApp number : Nat) (knownConfig : ClosKnown.Config)
    (oracle : CompileOracle (Nat × (Spt ValApprox × C))) (compiler : Compiler C)
    (program : List ClosLang.Exp) (optimized : List (ClosLang.Exp × ValApprox)) (globals : Spt ValApprox)
    (optimizedOutput : List ClosLang.Exp) (positive : 1 ≤ maxApp)
    (notFail : semantics ffi maxApp HolFiniteMapExact.holEmpty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (pureCc fvsInc (stateCc (ClosKnown.compileInc knownConfig)
          (pureCc ticksInc (pureCc letopInc compiler))))) program ≠ .fail)
    (numberSafe : ¬ containsAppSome maxApp program ∧
      ∀ n, (oracle n).2.2 = [] ∧ ¬ containsAppSome maxApp (oracle n).2.1)
    (knownSafe :
      let numberedCo := stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle
      let xs := (ClosNumber.renumberList number program).2
      syntaxOracleOk knownConfig xs numberedCo globals ∧
      ClosKnown.knownListTotal knownConfig (ClosFvs.compile xs) [] .ln = (optimized, globals))
    (optRun : ((optimized.map Prod.fst).mapM fun e => do
      let e ← ClosTicks.removeBounded fuel e
      ClosLetop.compileBounded fuel e) = some optimizedOutput) :
    semantics ffi maxApp HolFiniteMapExact.holEmpty (knownClosureFuture knownConfig oracle)
      compiler optimizedOutput =
    semantics ffi maxApp HolFiniteMapExact.holEmpty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (pureCc fvsInc (stateCc (ClosKnown.compileInc knownConfig)
          (pureCc ticksInc (pureCc letopInc compiler))))) program := by
  let numberedCo : CompileOracle (Spt ValApprox × C) := stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle
  let numbered := (ClosNumber.renumberList number program).2
  let co : CompileOracle (Spt ValApprox × C) := pureCo fvsInc ∘ numberedCo
  let transformed := ClosFvs.compile numbered
  let afterKnown := pureCc ticksInc (pureCc letopInc compiler)
  let knownCompiler := stateCc (ClosKnown.compileInc knownConfig) afterKnown
  have numberEq : semantics ffi maxApp HolFiniteMapExact.holEmpty numberedCo
      (pureCc fvsInc knownCompiler) numbered =
      semantics ffi maxApp HolFiniteMapExact.holEmpty oracle
        (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc) (pureCc fvsInc knownCompiler)) program :=
    ClosNumber.semanticsNumberHOL ffi maxApp number oracle (pureCc fvsInc knownCompiler)
      program notFail numberSafe
  have numberedNonfail : semantics ffi maxApp HolFiniteMapExact.holEmpty numberedCo
      (pureCc fvsInc knownCompiler) numbered ≠ .fail := by rw [numberEq]; exact notFail
  have numberedAux : ∀ n, (numberedCo n).2.2 = [] := by
    intro n
    simpa [numberedCo, stateCo, ClosNumber.ignoreTable] using (numberSafe.2 n).1
  have fvsEq : semantics ffi maxApp HolFiniteMapExact.holEmpty co knownCompiler transformed =
      semantics ffi maxApp HolFiniteMapExact.holEmpty numberedCo (pureCc fvsInc knownCompiler) numbered :=
    ClosFvs.semantics_compile ffi maxApp numberedCo knownCompiler numbered numberedNonfail ⟨numberedAux, positive⟩
  have fvsNonfail : semantics ffi maxApp HolFiniteMapExact.holEmpty co knownCompiler transformed ≠ .fail := by
    rw [fvsEq, numberEq]; exact notFail
  let knownCo : CompileOracle C := stateCo (ClosKnown.compileInc knownConfig) co
  have knownEq := ClosKnown.Semantics.semanticsKnownHOL knownConfig ffi maxApp co afterKnown transformed optimized globals
    fvsNonfail (syntaxOracleOk_fvsKnownPremises knownConfig numbered numberedCo globals optimized knownSafe.1 knownSafe.2)
  have knownNonfail : semantics ffi maxApp HolFiniteMapExact.holEmpty knownCo afterKnown
      (optimized.map Prod.fst) ≠ .fail := by rw [knownEq, fvsEq, numberEq]; exact notFail
  have knownAux : ∀ n, (knownCo n).2.2 = [] := by
    intro n
    simp [knownCo, stateCo, ClosKnown.compileInc, co, pureCo, fvsInc, ClosFvs.compileInc]
  let ticksCo : CompileOracle C := pureCo ticksInc ∘ knownCo
  let ticksOutput := ClosTicks.removeList (optimized.map Prod.fst)
  have ticksEq := ClosTicks.semantics_remove_ticks ffi maxApp knownCo
    (pureCc letopInc compiler) (optimized.map Prod.fst) knownNonfail ⟨knownAux, positive⟩
  have ticksNonfail : semantics ffi maxApp HolFiniteMapExact.holEmpty ticksCo
      (pureCc letopInc compiler) ticksOutput ≠ .fail := by
    rw [← ticksEq, knownEq, fvsEq, numberEq]; exact notFail
  have ticksAux : ∀ n, (ticksCo n).2.2 = [] := by simp [ticksCo, pureCo, ticksInc, ClosTicks.compileInc]
  let letopCo : CompileOracle C := pureCo letopInc ∘ ticksCo
  let letopOutput := ClosLetop.compileList ticksOutput
  have letopEq := ClosLetop.semantics_let_op ffi maxApp ticksCo compiler ticksOutput ticksNonfail ⟨ticksAux, positive⟩
  have outputEq := Option.some.inj ((ticks_letop_bounded fuel (optimized.map Prod.fst)).symm.trans optRun)
  have result := letopEq.trans (ticksEq.symm.trans (knownEq.trans (fvsEq.trans numberEq)))
  simpa [knownClosureFuture, letopCo, ticksCo, knownCo, co, numberedCo, letopOutput, ticksOutput, outputEq] using result

/-- Initial BVL labels are distinct after known-function optimization and
direct-call conversion of a numbered source program. -/
theorem knownCall_prepared_labels_nodup (fuel number : Nat) (knownConfig : ClosKnown.Config)
    (program : List ClosLang.Exp) (optimized : List (ClosLang.Exp × ValApprox)) (globals : Spt ValApprox)
    (optimizedOutput called : List ClosLang.Exp) (callState : ClosCall.State)
    (original current output : Config) (compiled : List (Nat × Nat × Bvl.Exp))
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (numberEven : number % 2 = 0) (numberLower : current.start + max 1 program.length ≤ number)
    (knownRun : ClosKnown.knownListTotal knownConfig (ClosFvs.compile (ClosNumber.renumberList number program).2)
      [] .ln = (optimized, globals))
    (optRun : ((optimized.map Prod.fst).mapM fun e => do
      let e ← ClosTicks.removeBounded fuel e
      ClosLetop.compileBounded fuel e) = some optimizedOutput)
    (callRun : ClosCall.compileFuel fuel true optimizedOutput = some (called, callState))
    (compile : compilePrepared? original current program
      (ClosAnnotate.compile (chainExps current.start called ++ callState.2)) = some (output, compiled, names)) :
    (compiled.map Prod.fst).Nodup := by
  have labels := numberedKnown_output_labels fuel number knownConfig program optimized globals optimizedOutput knownRun optRun
  have subset := numberedKnown_output_locations_subset fuel number knownConfig program optimized globals optimizedOutput knownRun optRun
  have sourceEven : ∀ loc ∈ codeLocations optimizedOutput, loc % 2 = 0 := by
    intro loc member
    have parity := ClosNumber.renumberList_location_parity program number loc (subset member)
    omega
  have sourceLower : ∀ loc ∈ codeLocations optimizedOutput, current.start + max 1 optimizedOutput.length ≤ loc := by
    intro loc member
    have bounds := labels.2.2 loc member
    omega
  have rawDistinct := initialCall_annotated_chain_source_nodup fuel current.start optimizedOutput called callState
    callRun labels.2.1 sourceEven sourceLower
  exact compilePrepared_labels_nodup_of_source original current output program
    (ClosAnnotate.compile (chainExps current.start called ++ callState.2)) compiled names compile rawDistinct

/-- Numbering and the known-function pipeline followed by direct-call and
BVL conversion preserve observations under the source and oracle safety
conditions. The initial known and direct-call pass results are explicit. -/
theorem knownCall_prepared_semantics {C F : Type} (ffi : HolFfiState F)
    (fuel relationFuel number : Nat) (knownConfig : ClosKnown.Config)
    (oracle : CompileOracle (Nat × (Spt ValApprox × (NumSet × C)))) (targetCompiler : BvlSem.Compiler C)
    (program : List ClosLang.Exp) (optimized : List (ClosLang.Exp × ValApprox)) (globals : Spt ValApprox)
    (optimizedOutput called : List ClosLang.Exp) (callState : ClosCall.State)
    (original current output : Config) (compiled : List (Nat × Nat × Bvl.Exp))
    (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (positive : 1 ≤ current.maxApp) (nonempty : program ≠ [])
    (numberEven : number % 2 = 0) (numberLower : current.start + max 1 program.length ≤ number)
    (oracleState : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
    (initialBound : (ClosNumber.renumberList number program).1 ≤ (oracle 0).1.1)
    (knownState : callState.1 = (knownClosureFuture knownConfig oracle 0).1.1)
    (nonfail : semantics ffi current.maxApp HolFiniteMapExact.holEmpty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (pureCc fvsInc (stateCc (ClosKnown.compileInc knownConfig)
          (pureCc ticksInc (pureCc letopInc
            (ClosCall.compileIncFuelCallback fuel (pureCc ClosAnnotate.compileInc
              (pureCc (compileInc current.maxApp) targetCompiler)))))))) program ≠ .fail)
    (numberSafe : ¬ containsAppSome current.maxApp program ∧
      ∀ n, (oracle n).2.2 = [] ∧ ¬ containsAppSome current.maxApp (oracle n).2.1)
    (knownSafe :
      let numberedCo := stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle
      let xs := (ClosNumber.renumberList number program).2
      syntaxOracleOk knownConfig xs numberedCo globals ∧
      ClosKnown.knownListTotal knownConfig (ClosFvs.compile xs) [] .ln = (optimized, globals))
    (optRun : ((optimized.map Prod.fst).mapM fun e => do
      let e ← ClosTicks.removeBounded fuel e
      ClosLetop.compileBounded fuel e) = some optimizedOutput)
    (callRun : ClosCall.compileFuel fuel true optimizedOutput = some (called, callState))
    (compile : compilePrepared? original current program
      (ClosAnnotate.compile (chainExps current.start called ++ callState.2)) = some (output, compiled, names)) :
    BvlSem.semantics ffi (sptFromAList compiled)
      (pureCo (compileInc current.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘
        ClosCall.compileIncFuelOracle fuel (knownClosureFuture knownConfig oracle)) targetCompiler output.start =
    semantics ffi current.maxApp HolFiniteMapExact.holEmpty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (pureCc fvsInc (stateCc (ClosKnown.compileInc knownConfig)
          (pureCc ticksInc (pureCc letopInc
            (ClosCall.compileIncFuelCallback fuel (pureCc ClosAnnotate.compileInc
              (pureCc (compileInc current.maxApp) targetCompiler)))))))) program := by
  let future := knownClosureFuture knownConfig oracle
  let compiler := ClosCall.compileIncFuelCallback fuel (pureCc ClosAnnotate.compileInc
    (pureCc (compileInc current.maxApp) targetCompiler))
  have knownEq := known_beforeCall_semantics ffi fuel current.maxApp number knownConfig oracle compiler
    program optimized globals optimizedOutput positive nonfail numberSafe knownSafe optRun
  have callSafe : semantics ffi current.maxApp HolFiniteMapExact.empty future compiler optimizedOutput ≠ .fail := by
    change semantics ffi current.maxApp HolFiniteMapExact.holEmpty (knownClosureFuture knownConfig oracle)
      compiler optimizedOutput ≠ .fail
    rw [knownEq]
    exact nonfail
  have numberedLocations : ∀ i, everyFnLocationSome
      (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle i).2.1 := by
    intro i
    simpa [stateCo, ClosNumber.ignoreTable] using
      ClosNumber.compileInc_locations (oracle i).1.1 (oracle i).2.1
  have knownLocations := ClosKnown.TraversalLocations.syntaxOracleOk_outputLocations knownConfig
    (ClosNumber.renumberList number program).2
    (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) globals optimized knownSafe.1
    (ClosNumber.renumberList_locations program number) numberedLocations knownSafe.2
  have knownVars := ClosKnown.TraversalSyntax.syntaxOracleOk_outputVarsNone knownConfig
    (ClosNumber.renumberList number program).2
    (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) globals optimized knownSafe.1 knownSafe.2
  have outputEq := Option.some.inj ((ticks_letop_bounded fuel (optimized.map Prod.fst)).symm.trans optRun)
  have outputLocations : everyFnLocationSome optimizedOutput := by
    rw [← outputEq]
    exact (ClosLetop.compileList_locations _).mpr ((ClosTicks.removeList_locations _).mpr knownLocations.1)
  have outputVars : everyFnVarsNone optimizedOutput := by
    rw [← outputEq]
    exact (ClosLetop.compileList_varsNone _).mpr ((ClosTicks.removeList_varsNone _).mpr knownVars.1)
  have outputLabels := numberedKnown_output_labels fuel number knownConfig program optimized globals optimizedOutput knownSafe.2 optRun
  have subset := numberedKnown_output_locations_subset fuel number knownConfig program optimized globals optimizedOutput knownSafe.2 optRun
  have outputSyntax : ClosCall.syntaxOk optimizedOutput := ⟨outputLocations, outputVars, outputLabels.2.1⟩
  have futureSyntax : ∀ i, ClosCall.syntaxOk (future i).2.1 ∧ (future i).2.2 = [] := by
    intro i
    constructor
    · refine ⟨?_, ?_, knownClosureFuture_codeLocations_nodup knownConfig oracle i⟩
      · simpa [future, knownClosureFuture, pureCo, letopInc, ticksInc, ClosLetop.compileInc, ClosTicks.compileInc] using
          (ClosLetop.compileList_locations _).mpr ((ClosTicks.removeList_locations _).mpr (knownLocations.2 i))
      · simpa [future, knownClosureFuture, pureCo, letopInc, ticksInc, ClosLetop.compileInc, ClosTicks.compileInc] using
          (ClosLetop.compileList_varsNone _).mpr ((ClosTicks.removeList_varsNone _).mpr (knownVars.2 i))
    · simp [future, knownClosureFuture, pureCo, letopInc, ClosLetop.compileInc]
  have outputNonempty : optimizedOutput ≠ [] := by
    intro empty
    have positiveLength := List.length_pos_iff.mpr nonempty
    simp [empty] at outputLabels
    omega
  have initialLower : ∀ loc ∈ codeLocations optimizedOutput, current.start + optimizedOutput.length ≤ loc := by
    intro loc member
    have bounds := outputLabels.2.2 loc member
    omega
  have initialUpper : ∀ loc ∈ codeLocations optimizedOutput, loc + 1 < (oracle 0).1.1 := by
    intro loc member
    have bounds := ClosNumber.renumberList_location_successor_bounds program number loc (subset member)
    omega
  have sourceEven : ∀ loc ∈ codeLocations optimizedOutput, loc % 2 = 0 := by
    intro loc member
    have parity := ClosNumber.renumberList_location_parity program number loc (subset member)
    omega
  have firstLower : current.start + optimizedOutput.length ≤ (oracle 0).1.1 := by
    have bound := ClosNumber.renumberList_start_le program number
    omega
  have futureLower : ∀ i loc, loc ∈ codeLocations (future i).2.1 → current.start + optimizedOutput.length ≤ loc := by
    intro i loc member
    have bounds := knownClosureFuture_location_bounds knownConfig oracle oracleState i loc member
    have between := numberingOracle_state_monotone oracle oracleState (Nat.zero_le i)
    omega
  have ordered : oracleMonotonic (fun entry => {loc | loc ∈ codeLocations entry.2.1}) (· < ·)
      {loc | loc ∈ codeLocations optimizedOutput} future := by
    constructor
    · intro i j x y order xmem ymem
      have xb := knownClosureFuture_location_bounds knownConfig oracle oracleState i x xmem
      have yb := knownClosureFuture_location_bounds knownConfig oracle oracleState j y ymem
      have between := numberingOracle_state_monotone oracle oracleState (show i + 1 ≤ j by omega)
      omega
    · intro i x y xmem ymem
      have xb := initialUpper x xmem
      have yb := knownClosureFuture_location_bounds knownConfig oracle oracleState i y ymem
      have between := numberingOracle_state_monotone oracle oracleState (Nat.zero_le i)
      omega
  have sourceLower : ∀ loc ∈ codeLocations optimizedOutput, current.start + max 1 optimizedOutput.length ≤ loc := by
    intro loc member
    have bound := initialLower loc member
    have positiveLength := List.length_pos_iff.mpr outputNonempty
    omega
  have rawDistinct := initialCall_annotated_chain_source_nodup fuel current.start optimizedOutput called callState
    callRun outputLabels.2.1 sourceEven sourceLower
  have compiledDistinct := compilePrepared_labels_nodup_of_source original current output program
    (ClosAnnotate.compile (chainExps current.start called ++ callState.2)) compiled names compile rawDistinct
  have chainBound : current.start + max 1 optimizedOutput.length ≤ (oracle 0).1.1 := by
    have positiveLength := List.length_pos_iff.mpr outputNonempty
    omega
  have limitPositive : 0 < (oracle 0).1.1 := by
    have positiveLength := List.length_pos_iff.mpr outputNonempty
    omega
  have rawBounds := initialCall_annotated_chain_source_below fuel current.start (oracle 0).1.1
    optimizedOutput called callState callRun chainBound initialUpper
  have initialBelow := compilePrepared_labels_below_of_source original current output program
    (ClosAnnotate.compile (chainExps current.start called ++ callState.2)) compiled names
    (oracle 0).1.1 limitPositive compile rawBounds.1 rawBounds.2
  have monotone : ∀ {i j}, i ≤ j → (oracle i).1.1 + numStubs current.maxApp ≤
      (oracle j).1.1 + numStubs current.maxApp := by
    intro i j order
    exact Nat.add_le_add_right (numberingOracle_state_monotone oracle oracleState order) _
  have callEq := call_to_preparedBvl_semantics_of_location_bounds ffi fuel relationFuel original current output
    targetCompiler (fun i => (oracle i).1.1 + numStubs current.maxApp)
    optimizedOutput called program callState compiled names future callRun outputSyntax knownState ordered futureSyntax
    outputNonempty initialLower futureLower callSafe compile compiledDistinct monotone initialBelow
    (knownCallOracle_bvl_labels_nodup current.maxApp fuel knownConfig oracle)
    (knownCallOracle_bvl_labels_range current.maxApp fuel knownConfig oracle oracleState)
  exact callEq.trans knownEq

end Flapjack.Compiler.Backend.ClosToBvl
