import Flapjack.Pancake.PanStructs.CompileExpProduction
import Flapjack.Pancake.PanStructs.CompileDeclsExact

/-! Flapjack codec infrastructure for declaration compilation. These
correspondences have no HOL theorem original; they connect production
carriers to the reviewed exact definitions without assuming compiler results. -/
namespace Flapjack
open Pancake.PanLang Basis.Pure.MlString

/-- Structure-name collection commutes with the context/declaration codecs.
The left-to-right traversal prepends every name, so duplicate declarations
retain the same shadowing order. Locals and globals are carried unchanged.
No name-range premise is needed: this operation does not compare names. -/
theorem structGetNames_encode {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width))) (context : StructPassContext) :
    structPassContextToExact (structGetNames context declarations) =
      Pancake.PanStructs.CompileShapeExact.getNamesExact
        (structPassContextToExact context) (declarations.map declToHOL) := by
  induction declarations generalizing context with
  | nil => rfl
  | cons declaration declarations ih =>
      cases declaration with
      | name name fields =>
          have hfields : fields.map paramToHOL =
              fields.map (fun p => (ofString p.1, shapeToHOL p.2)) := by
            apply List.map_congr_left
            intro p _
            cases p
            rfl
          simpa only [structGetNames, List.foldl_cons, List.map_cons, declToHOL,
            Pancake.PanStructs.CompileShapeExact.getNamesExact,
            structPassContextToExact, structContextToCompileShapeExact, hfields] using
            ih { context with structs := (name, { fields := fields, size := 0 }) :: context.structs }
      | function declaration =>
          simpa only [structGetNames, List.foldl_cons, List.map_cons, declToHOL,
            Pancake.PanStructs.CompileShapeExact.getNamesExact] using ih context
      | decl shape name value =>
          simpa only [structGetNames, List.foldl_cons, List.map_cons, declToHOL,
            Pancake.PanStructs.CompileShapeExact.getNamesExact] using ih context
      | exnDecl name shape =>
          simpa only [structGetNames, List.foldl_cons, List.map_cons, declToHOL,
            Pancake.PanStructs.CompileShapeExact.getNamesExact] using ih context

end Flapjack
