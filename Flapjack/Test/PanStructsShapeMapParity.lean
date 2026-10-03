import Flapjack.Pancake.Proofs.PanStructs.ShapeMap

namespace Flapjack.Test.PanStructsShapeMapParity
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanStructs.ShapeMap
open Flapjack.Basis.Pure.MlString

/-- Direct replay of the four original lookup observations, including duplicate
keys whose first binding wins (a left-fold update codec would fail this row). -/
def originalLookupRows : List Bool :=
  let entries : List (MlS × ShapeHOL) :=
    [(ofString "x", .comb [.one, .one]), (ofString "y", .one), (ofString "x", .one)]
  [ match (shapeMap entries).lookup (ofString "x") with
    | some (.comb [.one, .one]) => true
    | _ => false
  , match (shapeMap entries).lookup (ofString "y") with
    | some .one => true
    | _ => false
  , match (shapeMap entries).lookup (ofString "missing") with
    | none => true
    | _ => false
  , match (shapeMap []).lookup (ofString "x") with
    | none => true
    | _ => false ]

#eval originalLookupRows
#guard originalLookupRows = [true, true, true, true]
end Flapjack.Test.PanStructsShapeMapParity
