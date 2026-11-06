import Flapjack.Compiler.Backend.BviToData.Proofs.Build
import Flapjack.Compiler.Backend.BviToData.Proofs.State
import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux
import Flapjack.Misc.Sptree.Map

/-! Constant construction primitive simulation for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL
open Classical
noncomputable section

/-- The constant construction case of primitive application. This factored
simulation remains untagged pending review of the full source theorem and its
state carriers. -/
theorem doApp_build {C F : Type} (parts : List ClosLang.ConstPart)
    (args : List DataSem.Value) (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value)
    (next : BviSem.BviState C F)
    (run : BviSem.doApp (.blockOp (.build parts)) (args.map dataToBviValue) source =
      .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.blockOp (.build parts)) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | cons a rest =>
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
      BvlSem.doApp, BvlSem.applyBlock] at run
  | nil =>
    have refs : ∀ n, source.refs.lookup n = (sptLookup n target.refs).map dataToBviRef := by
      intro n
      rw [← sptLookup_sptMap]
      exact related.2.2.2.2.1 n
    have build := doBuildConst_projection parts target.refs source.refs target.tstamps refs
    cases dataRun : DataSem.doBuildConst parts target.refs target.tstamps with
    | mk value dataTail =>
      obtain ⟨dataRefs, stamps⟩ := dataTail
      cases bviRun : BvlSem.doBuildConst parts source.refs with
      | mk bviValue bviRefs =>
        simp only [dataRun, bviRun] at build
        simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
          BvlSem.doApp, BvlSem.applyBlock, BviSem.toBvl, bviRun] at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨{ target with refs := dataRefs, tstamps := stamps }, value, ?_, build.1, ?_⟩
        · simp [DataSem.doAppAux, DataSem.applyNonFfi, dataRun]
        · rcases related with ⟨clock, code, oracle, compiler, _, ffi, global⟩
          refine ⟨clock, code, oracle, compiler, ?_, ffi, global⟩
          intro key
          rw [sptLookup_sptMap]
          exact build.2 key

end
end Flapjack.Compiler.Backend.BviToData
