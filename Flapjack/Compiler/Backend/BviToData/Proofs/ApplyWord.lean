import Flapjack.Compiler.Backend.BviToData.Proofs.Word
import Flapjack.Compiler.Backend.BviToData.Proofs.State
import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux

/-! Word primitive simulation for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL
open Classical
noncomputable section

/-- The word operation case of primitive application, with the two byte
comparisons excluded in the HOL pass theorem. This factored simulation is
untagged pending review of the complete theorem and its state carriers. -/
theorem doApp_word {C F : Type} (op : ClosLang.WordOp) (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (notGt : op ≠ .wordTest .w8 (.compare .gt))
    (notGeq : op ≠ .wordTest .w8 (.compare .geq))
    (run : BviSem.doApp (.wordOp op) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.wordOp op) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases h : BvlSem.doWordApp op (args.map dataToBviValue) with
  | none =>
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
      BvlSem.doApp, BvlSem.applyNumeric, h] at run
  | some value =>
    obtain ⟨dataValue, dataRun, valueEq⟩ := doWordApp_bvi_success op args value notGt notGeq h
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
      BvlSem.doApp, BvlSem.applyNumeric, h, BviSem.fromBvl_toBvl] at run
    rcases run with ⟨rfl, rfl⟩
    refine ⟨target, dataValue, ?_, valueEq.symm, related⟩
    simp [DataSem.doAppAux, DataSem.applyNonFfi, dataRun]

end
end Flapjack.Compiler.Backend.BviToData
