import Flapjack.Compiler.Backend.BvlToBvi.Proofs.Divergence
import Flapjack.Compiler.Backend.BviToData.Proofs.Semantics

/-! Composition of the BVL-to-BVI and BVI-to-data semantic simulations. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack

/-- The executed BVL-to-BVI lowering followed by BVI-to-data compilation
preserves a non-failing BVL program's observable behavior. The source-program,
handler, and future-oracle conditions are the premises of the lowering proof.
This is Flapjack pipeline infrastructure pending HOL evaluator and carrier
reviews for the constituent simulations. -/
theorem compileProgFuel_toData_semantics {C F : Type}
    (fuel optFuel start counter : Nat) (ffi : HolFfiState F)
    (programs : List (Nat × Nat × Bvl.Exp))
    (oracle : BvlSem.CompileOracle (Nat × C)) (compiler : DataSem.Compiler C)
    (targetStart targetNextName : Nat) (targetProgram : List (Nat × Nat × Bvi.Exp))
    (limits : DataSem.Limits) (sizes : Spt Nat)
    (compiled : compileProgFuel fuel optFuel start counter programs = some (targetStart, targetProgram, targetNextName))
    (distinct : (programs.map Prod.fst).Nodup)
    (handlers : BvlHandle.Proofs.handleOk (programs.map (fun (_, _, body) => body)))
    (oracleHandlers : ∀ index, BvlHandle.Proofs.handleOk ((oracle index).2.map (fun (_, _, body) => body)))
    (counterBound : targetNextName ≤ (oracle 0).1.1)
    (nonfail : BvlSem.semantics ffi (sptFromAList programs) oracle
      (BackendProps.stateCc compileIncSource (fun cfg code => compiler cfg (BviToData.compileProg code))) start ≠ .fail) :
    DataSem.semantics ffi (sptFromAList (BviToData.compileProg targetProgram))
      (fun index => let (cfg, code) := BackendProps.stateCo compileIncSource oracle index
        (cfg, BviToData.compileProg code)) compiler limits sizes targetStart =
    BvlSem.semantics ffi (sptFromAList programs) oracle
      (BackendProps.stateCc compileIncSource (fun cfg code => compiler cfg (BviToData.compileProg code))) start := by
  let bviCompiler : BviSem.Compiler C := fun cfg code => compiler cfg (BviToData.compileProg code)
  let bviOracle := BackendProps.stateCo compileIncSource oracle
  have lowerSame := compileProgFuel_semantics fuel optFuel start counter ffi programs oracle bviCompiler
    targetStart targetNextName targetProgram compiled distinct handlers oracleHandlers counterBound nonfail
  have bviNonFail : BviSem.semantics ffi (sptFromAList targetProgram) bviOracle bviCompiler targetStart ≠ .fail := by
    rw [lowerSame]
    exact nonfail
  have dataSame := BviToData.compileProg_semantics ffi targetProgram bviOracle compiler limits sizes targetStart bviNonFail
  exact dataSame.trans lowerSame

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
