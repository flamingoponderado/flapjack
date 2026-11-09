import Flapjack.Compiler.Backend.BviToData.Proofs.Int
import Flapjack.Compiler.Backend.BviToData.Proofs.State
import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux

/-! Integer primitive simulation for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL
open Classical
noncomputable section

private theorem doApp_int_nonconst {C F : Type} (op : ClosLang.IntOp)
    (args : List DataSem.Value) (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (notConst : ∀ n, op ≠ .const n)
    (run : BviSem.doApp (.intOp op) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.intOp op) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  have fallback : BviSem.doAppAux (.intOp op) (args.map dataToBviValue) source = some none := by
    cases op <;> simp_all [BviSem.doAppAux]
  have projection := doIntApp_projection_nonconst op args notConst
  cases dataRun : DataSem.doIntApp op args with
  | none =>
    simp only [dataRun, Option.map_none] at projection
    simp [BviSem.doApp, BviSem.doAppFallback, fallback, BvlSem.doApp,
      BvlSem.applyNumeric, ← projection] at run
  | some value =>
    simp only [dataRun, Option.map_some] at projection
    simp [BviSem.doApp, BviSem.doAppFallback, fallback, BvlSem.doApp,
      BvlSem.applyNumeric, ← projection, BviSem.fromBvl_toBvl] at run
    rcases run with ⟨rfl, rfl⟩
    refine ⟨target, value, ?_, rfl, related⟩
    simp [DataSem.doAppAux, DataSem.applyNonFfi, dataRun]

/-- The integer operation case of primitive application. The constant case
uses the same small-integer guard as data semantics. This factored simulation
is untagged pending review of the complete HOL theorem and state carriers. -/
theorem doApp_int {C F : Type} (op : ClosLang.IntOp) (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.intOp op) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.intOp op) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases op with
  | const n =>
    cases args with
    | cons a rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
    | nil =>
      by_cases small : BackendCommon.smallEnoughInt n
      · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, small] at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨target, .number n, ?_, ?_, related⟩
        · simp [DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doIntApp, small]
        · simp [dataToBviValue]
      · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, small] at run
  | add | sub | mult | div | mod | less | lessEq | greater | greaterEq | lessConstSmall _ =>
    exact doApp_int_nonconst _ args source target related result next (by intro n; simp) run

end
end Flapjack.Compiler.Backend.BviToData
