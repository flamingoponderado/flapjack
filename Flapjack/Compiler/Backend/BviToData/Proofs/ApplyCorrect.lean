module

public import Flapjack.Compiler.Backend.BviToData.Proofs.Apply

@[expose] public section

/-! Source-statement primitive application correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

/- The canonical BVI reference carrier and its broad view roundtrip. -/
namespace ApplyCorrectCarrier

theorem holFmapAsFiniteSupportRelationWitness_BviState {C F : Type} :
    (∀ state : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad state).toBroad = state) ∧
    (∀ state : BviSem.BviState C F, BviSem.BviState.ofBroad state.toBroad = state) :=
  BviSem.holFmapAsFiniteSupportWitness

end ApplyCorrectCarrier

/-- Successful supported BVI primitive applications have the corresponding
DATA auxiliary result and related final state. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "data_to_bvi_do_app"
  (fmap_as_finite_support_relation := [BviState.refs])]
theorem dataToBvi_doApp {C F : Type} (op : ClosLang.Op)
    (target : DataSem.State C F) (source : BviSem.BviState C F)
    (args : List DataSem.Value) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (notInstall : op ≠ .install)
    (notGreater : op ≠ .intOp .greater)
    (notGreaterEq : op ≠ .intOp .greaterEq)
    (notWordGt : op ≠ .wordOp (.wordTest .w8 (.compare .gt)))
    (notWordGeq : op ≠ .wordOp (.wordTest .w8 (.compare .geq)))
    (_notCopyByte : ∀ b, op ≠ .memOp (.copyByte b))
    (notForce : op ≠ .thunkOp .forceThunk)
    (related : stateRel source target)
    (run : BviSem.doApp op (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value, DataSem.doAppAux op args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext :=
  doApp_projection op target source args result next notInstall notGreater notGreaterEq
    notWordGt notWordGeq notForce related run

end Flapjack.Compiler.Backend.BviToData
