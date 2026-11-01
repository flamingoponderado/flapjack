import Flapjack.Compiler.Backend.BviToData.Proofs.Equality
import Flapjack.Compiler.Backend.BviToData.Proofs.State
import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux

/-! Equality primitive simulation for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL
open Classical
noncomputable section

/-- The equality case of primitive application. This factored simulation is
untagged pending review of the complete primitive-application theorem and its
state carriers. -/
theorem doApp_equal {C F : Type} (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value)
    (next : BviSem.BviState C F)
    (run : BviSem.doApp (.blockOp .equal) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.blockOp .equal) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
      BvlSem.doApp, BvlSem.applyBlock] at run
  | cons a tail =>
    cases tail with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
        BvlSem.doApp, BvlSem.applyBlock] at run
    | cons b rest =>
      cases rest with
      | cons c rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
          BvlSem.doApp, BvlSem.applyBlock] at run
      | nil =>
        have refs : ∀ n, source.refs.lookup n = sptLookup n (sptMap dataToBviRef target.refs) :=
          related.2.2.2.2.1
        have eq := doEqProjection target.refs source.refs refs a b
        cases h : DataSem.doEq target.refs a b with
        | typeError =>
          simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
            BvlSem.doApp, BvlSem.applyBlock, BviSem.toBvl, eq, h] at run
        | val bool =>
          simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
            BvlSem.doApp, BvlSem.applyBlock, BviSem.toBvl, eq, h] at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨target, DataSem.boolValue bool, ?_, ?_, related⟩
          · simp [DataSem.doAppAux, DataSem.applyNonFfi, h]
          · exact (dataToBviValue_bool bool).symm

end
end Flapjack.Compiler.Backend.BviToData
