import Flapjack.Compiler.Backend.BvlToBvi.Proofs.MemoryOk
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.GlobalOk
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.ThunkOk

/-! Complete BVL primitive-application well-formedness. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value State doApp)

namespace ApplyAllCarrier
/-- Canonical BVL reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end ApplyAllCarrier

/-- Successful primitive application preserves state and result
well-formedness and any previously well-formed environment. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "do_app_ok"
  (fmap_as_finite_support := [refs])]
theorem doApp_ok {C F : Type} (op : ClosLang.Op)
    (args env : List Value) (s t : Flapjack.Compiler.Backend.BvlSem.State C F) (value : Value)
    (ok : stateOk s) (argsOk : bvOkList s.refs args)
    (run : doApp op args s = .val (value, t)) :
    stateOk t ∧ bvOk t.refs value ∧ (bvOkList s.refs env → bvOkList t.refs env) := by
  cases op with
  | label index => exact doApp_ok_label index args env s t value ok argsOk run
  | ffi name => exact doApp_ok_ffi name args env s t value ok argsOk run
  | intOp op => exact doApp_ok_int op args env s t value ok argsOk run
  | wordOp op => exact doApp_ok_word op args env s t value ok argsOk run
  | blockOp op => exact doApp_ok_block op args env s t value ok argsOk run
  | globOp op => exact doApp_ok_global op args env s t value ok argsOk run
  | memOp op => exact doApp_ok_memory op args env s t value ok argsOk run
  | install => exact doApp_ok_install args env s t value ok argsOk run
  | thunkOp op => exact doApp_ok_thunk op args env s t value ok argsOk run

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
