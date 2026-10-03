import Flapjack.Pancake.Semantics.PanCommonProps
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap
namespace Flapjack.Pancake.Proofs.PanStructs.ShapeMap
open Flapjack
open Flapjack.Pancake.PanLang

/-- Flapjack canonical rendering of external HOL alistTheory alist_to_fmap:
right-fold updates preserve the first binding, including duplicate keys. This
helper has no CakeML declaration of its own and carries no HOL tag. -/
def shapeMap (entries : List (MlS × ShapeHOL)) : HolFiniteMapExact MlS ShapeHOL :=
  entries.foldr (fun entry map => map.update entry) HolFiniteMapExact.empty

/-- Unconditional correspondence to the independent raw HOL-shaped right fold.
Representation infrastructure, not a separately tagged CakeML theorem. -/
theorem shapeMap_lookup (entries : List (MlS × ShapeHOL)) (key : MlS) :
    (shapeMap entries).lookup key = alistToFmap entries key := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    simp only [shapeMap, List.foldr_cons, HolFiniteMapExact.update, alistToFmap]
    change FUPDATE (shapeMap entries).lookup entry key = FUPDATE (alistToFmap entries) entry key
    simp only [FUPDATE]
    split <;> simp_all
end Flapjack.Pancake.Proofs.PanStructs.ShapeMap
