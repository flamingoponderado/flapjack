import Flapjack.Compiler.Backend.BvlToBvi.Proofs.TailrecNames
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.OptimizedProgram

/-! Semantic composition of BVL lowering and BVI tail-recursion elimination. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BviTailrec
open Flapjack.Compiler.Backend.BvlInline.Proofs

/-- The future-program optimizer preserves every oracle entry's ordered
labels. -/
theorem optimizedOracle_names {C : Type} (inlineLimit cutSize : Nat) (splitSeq : Bool)
    (oracle : BvlSem.CompileOracle (Spt (Nat × Bvl.Exp) × C)) (index : Nat) :
    ((letOpOracle splitSeq cutSize (removeTicksCo ∘ inCo inlineLimit oracle) index).2.map Prod.fst) =
      ((oracle index).2.map Prod.fst) := by
  cases entry : oracle index with
  | mk config program =>
    rcases config with ⟨cache, rest⟩
    have names := BvlInline.mapFstTickInlineAll inlineLimit cache program
    simpa [letOpOracle, removeTicksCo, Function.comp_def, inCo, entry, BvlInline.tickCompileProg,
      List.map_map] using names

/-- The optimizer removes only its own cache component from each future
compiler configuration. -/
theorem optimizedOracle_config {C : Type} (inlineLimit cutSize : Nat) (splitSeq : Bool)
    (oracle : BvlSem.CompileOracle (Spt (Nat × Bvl.Exp) × C)) (index : Nat) :
    (letOpOracle splitSeq cutSize (removeTicksCo ∘ inCo inlineLimit oracle) index).1 =
      (oracle index).1.2 := by
  cases entry : oracle index with
  | mk config program => cases config; simp [letOpOracle, removeTicksCo, Function.comp_def, inCo, entry]

/-- Production BVL-to-BVI lowering followed by tail-recursion elimination
preserves the behavior of a non-failing BVL program. Future oracle label and
worker-counter conditions are explicit. This source-shaped composition is
untagged pending evaluator and carrier review. -/
theorem lowerThenTailrec_semantics {C F : Type}
    (fuel optFuel start counter targetStart targetCounter : Nat) (enabled : Bool)
    (ffi : HolFfiState F) (program : List (Nat × Nat × Bvl.Exp))
    (oracle : BvlSem.CompileOracle (Nat × (Nat × C))) (compiler : BviSem.Compiler C)
    (lowered compiled : List (Nat × Nat × Bvi.Exp)) (last : Nat)
    (lowerRun : BvlToBvi.compileProgFuel fuel optFuel start counter program = some (targetStart, lowered, targetCounter))
    (tailRun : BviTailrec.compileProgFuel fuel enabled (bvlNumStubs + 2) lowered = some (last, compiled))
    (distinct : (program.map Prod.fst).Nodup)
    (handlers : BvlHandle.Proofs.handleOk (program.map (fun (_, _, body) => body)))
    (oracleHandlers : ∀ n, BvlHandle.Proofs.handleOk ((oracle n).2.map (fun (_, _, body) => body)))
    (oracleDistinct : ∀ n, ((oracle n).2.map Prod.fst).Nodup)
    (oracleNextBound : ∀ n, bvlNumStubs ≤ (oracle n).1.2.1)
    (oracleWorker : ∀ n, inWorkerNamespace (oracle n).1.2.1)
    (lowerCounterBound : targetCounter ≤ (oracle 0).1.1)
    (tailCounterBound : last ≤ (oracle 0).1.2.1)
    (nonFail : BvlSem.semantics ffi (sptFromAList program) oracle
      (BackendProps.stateCc compileIncSource (BackendProps.stateCc (compileProgSource enabled) compiler)) start ≠ .fail) :
    BviSem.semantics ffi (sptFromAList compiled)
        (BackendProps.stateCo (compileProgSource enabled) (BackendProps.stateCo compileIncSource oracle))
        compiler targetStart =
      BvlSem.semantics ffi (sptFromAList program) oracle
        (BackendProps.stateCc compileIncSource (BackendProps.stateCc (compileProgSource enabled) compiler)) start := by
  have lowerSame := compileProgFuel_semantics fuel optFuel start counter ffi program oracle
    (BackendProps.stateCc (compileProgSource enabled) compiler) targetStart targetCounter lowered lowerRun
    distinct handlers oracleHandlers lowerCounterBound nonFail
  have lowerNonFail : BviSem.semantics ffi (sptFromAList lowered)
      (BackendProps.stateCo compileIncSource oracle)
      (BackendProps.stateCc (compileProgSource enabled) compiler) targetStart ≠ .fail := by
    rw [lowerSame]
    exact nonFail
  have futureCondition := lowered_oracle_tailrec_inputCondition oracle oracleDistinct oracleNextBound oracleWorker
  have tailSame := lowering_tailrec_semantics fuel optFuel start counter targetStart targetCounter enabled
    program lowered compiled last ffi (BackendProps.stateCo compileIncSource oracle) compiler targetStart
    distinct lowerRun tailRun futureCondition tailCounterBound lowerNonFail
  exact tailSame.symm.trans lowerSame

/-- The production BVL optimizer, BVL-to-BVI lowering, and BVI
tail-recursion elimination preserve whole-program behavior in sequence.
This composition remains untagged pending the HOL evaluator and carrier
reviews for the underlying pass theorems. -/
theorem optimizedLowerTailrec_semantics {C F : Type}
    (bvlFuel inlineLimit cutSize bviFuel optFuel start counter : Nat) (splitSeq enabled : Bool)
    (ffi : HolFfiState F) (program : List (Nat × Nat × Bvl.Exp))
    (oracle : BvlSem.CompileOracle (Spt (Nat × Bvl.Exp) × (Nat × (Nat × C))))
    (compiler : BviSem.Compiler C) (cache : Spt (Nat × Bvl.Exp))
    (optimized : List (Nat × Nat × Bvl.Exp)) (targetStart targetCounter : Nat)
    (lowered compiled : List (Nat × Nat × Bvi.Exp)) (last : Nat)
    (optimizedRun : BvlInline.compileProgFuel bvlFuel inlineLimit cutSize splitSeq program = some (cache, optimized))
    (lowerRun : BvlToBvi.compileProgFuel bviFuel optFuel start counter optimized = some (targetStart, lowered, targetCounter))
    (tailRun : BviTailrec.compileProgFuel bviFuel enabled (bvlNumStubs + 2) lowered = some (last, compiled))
    (cacheEq : (oracle 0).1.1 = cache)
    (distinct : (program.map Prod.fst).Nodup)
    (oracleDistinct : ∀ n, ((oracle n).2.map Prod.fst).Nodup)
    (oracleNextBound : ∀ n, bvlNumStubs ≤ (oracle n).1.2.2.1)
    (oracleWorker : ∀ n, inWorkerNamespace (oracle n).1.2.2.1)
    (lowerCounterBound : targetCounter ≤ (oracle 0).1.2.1)
    (tailCounterBound : last ≤ (oracle 0).1.2.2.1)
    (nonFail : BvlSem.semantics ffi (sptFromAList program) oracle
      (inCc inlineLimit (removeTicksCc (letOpCompiler splitSeq cutSize
        (BackendProps.stateCc compileIncSource (BackendProps.stateCc (compileProgSource enabled) compiler))))) start ≠ .fail) :
    BviSem.semantics ffi (sptFromAList compiled)
        (BackendProps.stateCo (compileProgSource enabled)
          (BackendProps.stateCo compileIncSource
            (letOpOracle splitSeq cutSize (removeTicksCo ∘ inCo inlineLimit oracle)))) compiler targetStart =
      BvlSem.semantics ffi (sptFromAList program) oracle
        (inCc inlineLimit (removeTicksCc (letOpCompiler splitSeq cutSize
          (BackendProps.stateCc compileIncSource (BackendProps.stateCc (compileProgSource enabled) compiler))))) start := by
  let future := letOpOracle splitSeq cutSize (removeTicksCo ∘ inCo inlineLimit oracle)
  let downstream := BackendProps.stateCc compileIncSource (BackendProps.stateCc (compileProgSource enabled) compiler)
  have optimizedSame := BvlInline.Proofs.compileProgFuel_semantics bvlFuel inlineLimit cutSize start splitSeq
    ffi program oracle downstream cache optimized optimizedRun cacheEq distinct nonFail
  have optimizedDistinct : (optimized.map Prod.fst).Nodup := by
    rw [BvlInline.Proofs.compileProgFuel_names bvlFuel inlineLimit cutSize splitSeq program cache optimized optimizedRun]
    exact distinct
  have handlers := BvlInline.Proofs.compileProgFuel_handleOk bvlFuel inlineLimit cutSize splitSeq
    program cache optimized optimizedRun
  have futureHandlers : ∀ index, BvlHandle.Proofs.handleOk
      ((future index).2.map (fun (_, _, body) => body)) := by
    intro index
    exact letOpTransform_program_handleOk splitSeq cutSize ((removeTicksCo ∘ inCo inlineLimit oracle) index).2
  have futureDistinct : ∀ index, ((future index).2.map Prod.fst).Nodup := by
    intro index
    rw [optimizedOracle_names inlineLimit cutSize splitSeq oracle index]
    exact oracleDistinct index
  have futureBound : ∀ index, bvlNumStubs ≤ (future index).1.2.1 := by
    intro index
    rw [optimizedOracle_config inlineLimit cutSize splitSeq oracle index]
    exact oracleNextBound index
  have futureWorker : ∀ index, inWorkerNamespace (future index).1.2.1 := by
    intro index
    rw [optimizedOracle_config inlineLimit cutSize splitSeq oracle index]
    exact oracleWorker index
  have optimizedNonFail : BvlSem.semantics ffi (sptFromAList optimized) future downstream start ≠ .fail := by
    rw [optimizedSame]
    exact nonFail
  have lowerBound : targetCounter ≤ (future 0).1.1 := by
    rw [optimizedOracle_config inlineLimit cutSize splitSeq oracle 0]
    exact lowerCounterBound
  have tailBound : last ≤ (future 0).1.2.1 := by
    rw [optimizedOracle_config inlineLimit cutSize splitSeq oracle 0]
    exact tailCounterBound
  have combined := lowerThenTailrec_semantics bviFuel optFuel start counter targetStart targetCounter enabled
    ffi optimized future compiler lowered compiled last lowerRun tailRun optimizedDistinct handlers futureHandlers
    futureDistinct futureBound futureWorker lowerBound tailBound optimizedNonFail
  exact combined.trans optimizedSame

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
