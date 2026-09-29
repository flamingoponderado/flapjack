import Flapjack.HolRef
import Flapjack.Pancake.PanStructs.CompileShapeExact

/-! Exact proof theorem for the source `compile_shapes` definition. -/

namespace Flapjack.Pancake.Proofs.PanStructs.CompileShapeExact

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanStructs.CompileShapeExact

/-- HOL `compile_shapes_eq_map` (`pan_structsProofScript.sml:310`) over the
    faithful structure-list and shape carriers. Its statement has no added
    hypotheses or fuel argument. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_shapes_eq_map" 310]
theorem compileShapesExact_eq_map
    (sctxt : List (MlS × List (MlS × ShapeHOL))) :
    (compileShapesExact sctxt : List ShapeHOL → List ShapeHOL) =
      fun shapes => shapes.map (compileShapeExact sctxt) := by
  funext shapes
  induction shapes with
  | nil => simp [compileShapesExact]
  | cons shape shapes ih => simp [compileShapesExact, ih]

end Flapjack.Pancake.Proofs.PanStructs.CompileShapeExact
