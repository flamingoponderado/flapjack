import Flapjack.Pancake.Proofs.PanStructs.ConvertCode
namespace Flapjack.Pancake.Proofs.PanStructs.ConvertCodeLocals
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanStructs.CompileShapeExact

/-- Full original arbitrary locals-update neutrality. Converted function bodies
replace context.locals with the original parameter list, so changing the caller
locals cannot change the compiled code map. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "convert_code_locals_upd"
  (fmap_as_finite_support_relation := [code])
  (words_as_type_indexed_bitvec)]
theorem convertCodeLocalsUpd {width : Nat} [NeZero width] {κ : Type}
    (context : ContextExact) (f : List (MlS × ShapeHOL) → List (MlS × ShapeHOL))
    (code : HolFiniteMapExact κ (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) :
    convertCodeExact {context with locals := f context.locals} code =
      convertCodeExact context code := by
  rfl
end Flapjack.Pancake.Proofs.PanStructs.ConvertCodeLocals
