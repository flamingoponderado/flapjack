module

public import Flapjack.Compiler.Backend.BviToData.Proofs.Finalise
public import Flapjack.Compiler.Backend.BviToData.Proofs.State
public import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
public import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux
public import Flapjack.Misc.Sptree.Map

@[expose] public section

/-! Mutable-constructor finalization simulation for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL
open Classical
noncomputable section

/-- Successful BVI finalization is simulated by data finalization, preserving
the resulting references and value projection. This factored case is
untagged pending review of the complete primitive theorem. -/
theorem doApp_finaliseCons {C F : Type} (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.memOp .finaliseCons) (args.map dataToBviValue) source =
      .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.memOp .finaliseCons) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
      BvlSem.doApp, BvlSem.applyMemory] at run
  | cons arg rest =>
    cases rest with
    | cons a rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
        BvlSem.doApp, BvlSem.applyMemory] at run
    | nil =>
      have refs : ∀ n, source.refs.lookup n = (sptLookup n target.refs).map dataToBviRef := by
        intro n
        rw [← sptLookup_sptMap]
        exact related.2.2.2.2.1 n
      cases final : BviSem.finaliseCons (dataToBviValue arg) source.refs with
      | none => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, final] at run
      | some pair =>
        obtain ⟨bviValue, bviRefs⟩ := pair
        obtain ⟨dataValue, dataRefs, stamps, dataRun, valueEq, refsEq⟩ :=
          finaliseCons_projection arg target.refs target.tstamps source.refs bviValue bviRefs refs final
        simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, final] at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨{ target with refs := dataRefs, tstamps := stamps }, dataValue, ?_, valueEq, ?_⟩
        · simp [DataSem.doAppAux, DataSem.applyNonFfi, dataRun]
        · rcases related with ⟨clock, code, oracle, compiler, _, ffi, global⟩
          refine ⟨clock, code, oracle, compiler, ?_, ffi, global⟩
          intro key
          rw [sptLookup_sptMap]
          exact refsEq key

end
end Flapjack.Compiler.Backend.BviToData
