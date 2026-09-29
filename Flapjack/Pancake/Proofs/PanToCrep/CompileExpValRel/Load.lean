import Flapjack.Pancake.Proofs.PanToCrep.CompileExpValRel
import Flapjack.Pancake.Semantics.PanSem.TotalEvalExpBridge

/-!
# Production RV64 `Load` bridge for `compile_exp_val_rel`

This is Flapjack proof infrastructure for the `Load` case of HOL
`compile_exp_val_rel` (`pan_to_crepProofScript.sml:217-256`). It composes the
production RV64 source expression evaluator with the exact-carrier `Load` case
in `CompileExpValRel.lean`. The state relation and rangedness premise are the
existing production/exact representation bridge obligations; every HOL shape
constructor is admitted, with no `One`/flat-`Two` restriction. This is
Flapjack-specific infrastructure with no standalone HOL declaration: HOL's
source `Load` case is proved inside `compile_exp_val_rel`, while this theorem
also relates the executable RV64 evaluator to the exact evaluator and carrier.
The direct HOL-shaped constructor lemma is `compileExpValRelHOL_load` in
`CompileExpValRel.lean`; the complete parent theorem is assembled separately.
-/

namespace Flapjack
namespace CompileExpValRelProduction

open Flapjack.Pancake.PanLang

/-- Flapjack-specific bridge from production RV64 evaluation to the exact
carrier's staged `Load` case for every `ShapeHOL`. The address
induction hypothesis and all other premises are precisely those consumed by
the exact case lemma; no target-evaluation fact is assumed. The source
successful-evaluation premise is discharged by the all-constructor
`evalPanSemStateExp_agree` bridge. `expOfHOL_byteRanged_bridge` discharges the
production evaluator's codec premise for all exact shapes, including nested
named shapes. -/
theorem compileExpValRelHOL_load_ofProductionRV64 {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (context : PanToCrepContextExact 64)
    (targetState : CrepSemHOLState 64 σ) [DecidablePred targetState.memaddrs]
    (shape : ShapeHOL) (address : ExpHOL 64) (value : PanValue (RiscV.Word 64))
    (expressions : List (CrepExpHOL 64)) (outputShape : ShapeHOL)
    (hsub : ∀ (subValue : ValueHOL 64) (subExpressions : List (CrepExpHOL 64))
        (subShape : ShapeHOL),
        exact.evalHOLFinite address = some subValue →
        panToCrepStateRelFiniteExact exact targetState →
        codeRelExactHOLW context exact.code targetState.code →
        panToCrepLocalsRelFiniteExact context exact.locals targetState.locals →
        localisedExpHOL address = true →
        compileExpExactHOLW context address = (subExpressions, subShape) →
        subExpressions.map (evalCrepSemHOLExp targetState) = (flattenHOL subValue).map some ∧
        subExpressions.length = sizeOfShapeHOL subShape ∧
        shapeOfHOLExact subValue = subShape ∧
        isWfShapeExactHOL ([] : StructContextExact) subShape = true)
    (heval : evalPanSemStateExp production (expOfHOL (.load shape address)) = some value)
    (hrel : PanSemStateRelExec production exact.toExact)
    (hranged : PanSemStateRelExecRanged production)
    (hlocalised : localisedExpHOL (.load shape address) = true)
    (hstate : panToCrepStateRelFiniteExact exact targetState)
    (hcode : codeRelExactHOLW context exact.code targetState.code)
    (hlocals : panToCrepLocalsRelFiniteExact context exact.locals targetState.locals)
    (hcompile : compileExpExactHOLW context (.load shape address) =
      (expressions, outputShape)) :
    expressions.map (evalCrepSemHOLExp targetState) =
        (flattenHOL (panValueToHOL value)).map some ∧
      expressions.length = sizeOfShapeHOL outputShape ∧
      shapeOfHOLExact (panValueToHOL value) = outputShape ∧
      isWfShapeExactHOL ([] : StructContextExact) outputShape = true := by
  have hbyteRanged := expOfHOL_byteRanged_bridge (.load shape address)
  have hagree := evalPanSemStateExp_agree production exact hrel hranged
    (expOfHOL (.load shape address)) hbyteRanged
  simp only [expToHOL_expOfHOL] at hagree
  rw [heval] at hagree
  have hexact : exact.evalHOLFinite (.load shape address) =
      some (panValueToHOL value) := hagree.symm
  exact compileExpValRelHOL_load exact context targetState shape address
    (panValueToHOL value) expressions outputShape hsub hexact hlocalised hstate
    hcode hlocals hcompile

end CompileExpValRelProduction
end Flapjack
