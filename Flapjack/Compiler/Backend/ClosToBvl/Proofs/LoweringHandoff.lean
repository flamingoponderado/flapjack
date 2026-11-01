import Flapjack.Compiler.Backend.ClosToBvl.Proofs.AnnotationCodeSemantics
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.Divergence

/-! Behavior composition from unoptimized closure conversion through BVI lowering. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.BackendProps

/-- The production closure driver with optional closure optimizations disabled,
followed by checked BVL-to-BVI lowering, preserves proof-side source behavior.
The source safety, handler and oracle conditions remain explicit; this is not a
reviewed HOL theorem or a full CakeML-to-target correctness statement. -/
theorem noOpts_closure_lowering_semantics {C F : Type} (ffi : HolFfiState F)
    (closureFuel lowerFuel optFuel : Nat) (config current output : Config)
    (expressions : List ClosLang.Exp) (program : List (Nat × Nat × ClosLang.Exp))
    (compiled : List (Nat × Nat × Bvl.Exp)) (names : Spt Flapjack.Basis.Pure.MlString.MlString)
    (oracle : ClosSem.CompileOracle (Nat × (Nat × C))) (compiler : BviSem.Compiler C)
    (targetStart targetNext : Nat) (lowered : List (Nat × Nat × Bvi.Exp))
    (mti : config.doMti = false) (calls : config.doCall = false) (known : config.knownConf = none)
    (preprocess : compileCommonNoOpts? config expressions = some (current, program))
    (closureRun : compileCallMtiFuel? closureFuel config expressions = some (output, compiled, names))
    (lowerRun : BvlToBvi.compileProgFuel lowerFuel optFuel output.start 0 compiled =
      some (targetStart, lowered, targetNext))
    (nonfail : semantics ffi config.maxApp HolFiniteMapExact.empty oracle
      (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
        (pureCc ClosAnnotate.compileInc (pureCc (compileInc config.maxApp)
          (stateCc BvlToBvi.compileIncSource compiler)))) expressions ≠ .fail)
    (numberSafe : ¬ containsAppSome config.maxApp expressions) (varsSafe : everyFnVarsNone expressions)
    (oracleSafe : ∀ index, (oracle index).2.2 = [] ∧
      ¬ containsAppSome config.maxApp (oracle index).2.1 ∧ everyFnVarsNone (oracle index).2.1)
    (oracleState : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)
    (initialBound : current.nextLoc ≤ (oracle 0).1.1)
    (handlers : BvlHandle.Proofs.handleOk (compiled.map (fun (_, _, body) => body)))
    (oracleHandlers : ∀ index, BvlHandle.Proofs.handleOk
      (((pureCo (compileInc config.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘
        stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) index).2.map (fun (_, _, body) => body)))
    (counterBound : targetNext ≤ ((pureCo (compileInc config.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘
      stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) 0).1.1) :
    BviSem.semantics ffi (sptFromAList lowered)
      (stateCo BvlToBvi.compileIncSource (pureCo (compileInc config.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘
        stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle)) compiler targetStart =
      semantics ffi config.maxApp HolFiniteMapExact.empty oracle
        (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
          (pureCc ClosAnnotate.compileInc (pureCc (compileInc config.maxApp)
            (stateCc BvlToBvi.compileIncSource compiler)))) expressions := by
  let bvlOracle := pureCo (compileInc config.maxApp) ∘ pureCo ClosAnnotate.compileInc ∘
    stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle
  have closureEq := compileCallMtiFuel_noOpts_semantics ffi closureFuel config current output expressions
    program compiled names oracle (stateCc BvlToBvi.compileIncSource compiler) mti calls known preprocess closureRun
    nonfail numberSafe varsSafe oracleSafe oracleState initialBound
  have bvlNonfail : BvlSem.semantics ffi (sptFromAList compiled) bvlOracle
      (stateCc BvlToBvi.compileIncSource compiler) output.start ≠ .fail := by
    rw [closureEq]
    exact nonfail
  have noOptsRun : compileNoOpts? config expressions = some (output, compiled, names) := by
    simpa [← compileCallMtiFuel_noOpts closureFuel config expressions mti calls known] using closureRun
  have distinct := compileNoOpts_prepared_labels_nodup config current output expressions program compiled names
    preprocess noOptsRun
  have loweredEq := BvlToBvi.Proofs.compileProgFuel_semantics lowerFuel optFuel output.start 0 ffi
    compiled bvlOracle compiler targetStart targetNext lowered lowerRun distinct handlers oracleHandlers counterBound bvlNonfail
  exact loweredEq.trans closureEq

end Flapjack.Compiler.Backend.ClosToBvl
