import Flapjack.Pancake.PanStructs.CompileShapeExact
import Flapjack.Pancake.Semantics.CrepSem.HOLState
namespace Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

/-- Full HOL exception-shape conversion, preserving keys and domain. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "convert_eshapes_def"
  (fmap_as_finite_support_result)]
def convertEshapesExact {α β : Type} (structContext : List (MlS × List (α × ShapeHOL)))
    (eshapes : Flapjack.HolFiniteMapExact β ShapeHOL) :
    Flapjack.HolFiniteMapExact β ShapeHOL :=
  eshapes.map2 (fun entry => compileShapeExact structContext entry.2)

/-- Flapjack lookup codec for the independent HOL-shaped raw map operation.
It is infrastructure rather than a HOL declaration over unrestricted maps. -/
def convertEshapesRaw {α β : Type} (structContext : List (MlS × List (α × ShapeHOL)))
    (eshapes : β → Option ShapeHOL) (key : β) : Option ShapeHOL :=
  (eshapes key).map (compileShapeExact structContext)

/-- Canonical-to-raw lookup correspondence, with no correspondence premise. -/
theorem holFmapAsFiniteSupportResultWitness_convertEshapesExact {α β : Type}
    (structContext : List (MlS × List (α × ShapeHOL)))
    (eshapes : Flapjack.HolFiniteMapExact β ShapeHOL) (key : β) :
    (convertEshapesExact structContext eshapes).lookup key =
      convertEshapesRaw structContext eshapes.lookup key := rfl
end Flapjack.Pancake.PanStructs.CompileShapeExact
