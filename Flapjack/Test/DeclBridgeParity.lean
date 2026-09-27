import Flapjack.Pancake.Semantics.PanSem.NameDeclBridge

/-! Kernel regressions for the declarator/expression bridge theorems in
`Flapjack.Pancake.Semantics.PanSem.NameDeclBridge`.

The expected values are recorded by direct HOL EVAL of the source evaluator in
`scripts/hol-probes/pan_sem_state_eval_probe.out`: the Load rows
`word_load_hit=SOME (ValWord 0x1122334455667788w)` and `word_load_miss=NONE`
(success and memory-domain rejection). The broad-carrier Lean guards for those
same HOL rows live in `Flapjack/Test/PanSemStateEvalParity.lean`; the examples
below exercise the finite-support bridge statements themselves. -/

namespace Flapjack.Test.DeclBridgeParity

open Flapjack
open Flapjack.Pancake.PanLang

/-- Finite-support Load `.one` bridge (success case): applying the correspondence
    theorem under an abstract memory/address correspondence. Paired with the
    `word_load_hit` direct HOL row. -/
example (state : PanSemStateFiniteExact 64 Unit) [DecidablePred state.memaddrs]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64)))
    (baseAddress topAddress bytesInWord : RiscV.Word 64)
    (addressExpression : Exp (RiscV.Word 64))
    (hMem : PanValueMemoryCodecRel memory state)
    (haddr : PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        addressExpression (memoryAccess := none))
      (state.evalHOLFinite (expToHOL addressExpression))) :
    PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        (.load .one addressExpression) (memoryAccess := none))
      (state.evalHOLFinite (.load .one (expToHOL addressExpression))) :=
  evalPanValueExp_load_one_option_correspondence state structs locals globals memory
    baseAddress topAddress bytesInWord addressExpression hMem haddr

/-- Executed RV64 `.op` option-level bridge (success and failed-argument lists):
    no successful-argument-list premise, `wordOp` discharged at the executed
    access. Paired with the direct HOL rows `op_add_fold_three` (success) and
    `op_add_var_missing` / `op_sub_wrong_arity` (rejection). -/
example (productionState : PanSemState (RiscV.Word 64) Unit)
    (state : PanSemStateFiniteExact 64 Unit) [DecidablePred state.memaddrs]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64)))
    (baseAddress topAddress bytesInWord : RiscV.Word 64)
    (operator : BinOp) (arguments : List (Exp (RiscV.Word 64)))
    (hargs : ∀ e ∈ arguments,
      PanSemDeclarationValueOptionRel PanValueCodecRel
        (evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord e
          (memoryAccess := some (panSemBitVec64MemoryAccess productionState)))
        (state.evalHOLFinite (expToHOL e))) :
    PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        (.op operator arguments)
        (memoryAccess := some (panSemBitVec64MemoryAccess productionState)))
      (state.evalHOLFinite (.op operator (arguments.map expToHOL))) :=
  evalPanValueExp_op_option_correspondence_executed productionState state structs locals
    globals memory baseAddress topAddress bytesInWord operator arguments hargs


/-- Offset agreement used by the flat-Load recursion (`flapjack-rdc.2.1.1`). -/
example (address : BitVec 8) (k : Nat) :
    panValueFlatOffset (bytesInWordHOL 8) address k =
      address + bytesInWordHOL 8 * BitVec.ofNat 8 k :=
  panValueFlatOffset_bitvec_add address k

end Flapjack.Test.DeclBridgeParity
