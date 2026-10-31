import Flapjack.Compiler.Backend.BvlToBvi.Proofs.Divergence
import Flapjack.Compiler.Backend.BvlInline.Proofs.FullSemantics

/-! Composition of the production BVL optimizer with BVL-to-BVI lowering. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlInline.Proofs

/-- Production BVL optimization followed by BVL-to-BVI lowering preserves
the whole behavior of a non-failing source program. The optimizer supplies
the target pass's handler-shape preconditions for both initial and installed
code. This remains untagged pending evaluator and state-carrier HOL review. -/
theorem optimizedProgram_semantics {C F : Type}
    (bvlFuel inlineLimit cutSize bviFuel optFuel start counter : Nat) (splitSeq : Bool)
    (ffi : HolFfiState F) (program : List (Nat × Nat × Bvl.Exp))
    (oracle : BvlSem.CompileOracle (Spt (Nat × Bvl.Exp) × (Nat × C)))
    (compiler : BviSem.Compiler C)
    (cache : Spt (Nat × Bvl.Exp)) (optimized : List (Nat × Nat × Bvl.Exp))
    (targetStart targetNextName : Nat) (targetProgram : List (Nat × Nat × Bvi.Exp))
    (optimizedRun : BvlInline.compileProgFuel bvlFuel inlineLimit cutSize splitSeq program = some (cache, optimized))
    (loweredRun : compileProgFuel bviFuel optFuel start counter optimized = some (targetStart, targetProgram, targetNextName))
    (cacheEq : (oracle 0).1.1 = cache)
    (distinct : (program.map Prod.fst).Nodup)
    (counterBound : targetNextName ≤
      (letOpOracle splitSeq cutSize (removeTicksCo ∘ inCo inlineLimit oracle) 0).1.1)
    (nonFail : BvlSem.semantics ffi (sptFromAList program) oracle
      (inCc inlineLimit (removeTicksCc (letOpCompiler splitSeq cutSize
        (BackendProps.stateCc compileIncSource compiler)))) start ≠ .fail) :
    BviSem.semantics ffi (sptFromAList targetProgram)
      (BackendProps.stateCo compileIncSource
        (letOpOracle splitSeq cutSize (removeTicksCo ∘ inCo inlineLimit oracle))) compiler targetStart =
    BvlSem.semantics ffi (sptFromAList program) oracle
      (inCc inlineLimit (removeTicksCc (letOpCompiler splitSeq cutSize
        (BackendProps.stateCc compileIncSource compiler)))) start := by
  have optimizedSame := BvlInline.Proofs.compileProgFuel_semantics bvlFuel inlineLimit cutSize start splitSeq
    ffi program oracle (BackendProps.stateCc compileIncSource compiler) cache optimized optimizedRun cacheEq distinct nonFail
  have optimizedDistinct : (optimized.map Prod.fst).Nodup := by
    rw [BvlInline.Proofs.compileProgFuel_names bvlFuel inlineLimit cutSize splitSeq program cache optimized optimizedRun]
    exact distinct
  have handlers := BvlInline.Proofs.compileProgFuel_handleOk bvlFuel inlineLimit cutSize splitSeq
    program cache optimized optimizedRun
  have oracleHandlers : ∀ index, BvlHandle.Proofs.handleOk
      (((letOpOracle splitSeq cutSize (removeTicksCo ∘ inCo inlineLimit oracle)) index).2.map
        (fun (_, _, body) => body)) := by
    intro index
    exact letOpTransform_program_handleOk splitSeq cutSize ((removeTicksCo ∘ inCo inlineLimit oracle) index).2
  have optimizedNonFail : BvlSem.semantics ffi (sptFromAList optimized)
      (letOpOracle splitSeq cutSize (removeTicksCo ∘ inCo inlineLimit oracle))
      (BackendProps.stateCc compileIncSource compiler) start ≠ .fail := by
    rw [optimizedSame]
    exact nonFail
  have lowerSame := compileProgFuel_semantics bviFuel optFuel start counter ffi optimized
    (letOpOracle splitSeq cutSize (removeTicksCo ∘ inCo inlineLimit oracle)) compiler
    targetStart targetNextName targetProgram loweredRun optimizedDistinct handlers oracleHandlers counterBound optimizedNonFail
  exact lowerSame.trans optimizedSame

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
