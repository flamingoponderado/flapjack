import Flapjack.Pancake.PanGlobals.CompileExpExactRoute
import Flapjack.Pancake.PanLang.Prog.FreeVarIdsCodec

namespace Flapjack

open Flapjack.Basis.Pure.MlString Flapjack.Pancake.PanLang

/-- The generated initializer uses only zero constants and records. This
    Flapjack codec lemma has no separate HOL original. -/
private theorem cakeShapeVal_decode {width : Nat} [NeZero width]
    (context : CakeContext width) (shape : Shape) :
    cakeShapeVal context shape = expOfHOL (shapeValHOL (shapeToHOL shape)) := by
  fun_induction cakeShapeVal context shape <;>
    simp_all [shapeValHOL, shapeValsHOL_eq_map, shapeToHOL, expOfHOL, List.map_map]

end Flapjack
