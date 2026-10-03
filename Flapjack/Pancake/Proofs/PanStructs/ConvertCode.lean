import Flapjack.Pancake.PanStructs.CompileProgExact
import Flapjack.Pancake.Semantics.CrepSem.HOLState
namespace Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

/-- Full source code-map conversion. Original parameters scope the compiled body. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "convert_code_def"
  (fmap_as_finite_support_result) (words_as_type_indexed_bitvec)]
def convertCodeExact {width : Nat} [NeZero width] {κ : Type}
    (context : ContextExact)
    (code : Flapjack.HolFiniteMapExact κ (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) :
    Flapjack.HolFiniteMapExact κ (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL) :=
  code.map2 fun entry =>
    let parameters := entry.2.1
    (parameters.map (fun parameter => (parameter.1, compileShapeExact context.structs parameter.2)),
      compileProgExact { context with locals := parameters } entry.2.2.1,
      compileShapeExact context.structs entry.2.2.2)

/-- Flapjack-specific independent raw lookup rendering of the source FMAP_MAP2
operation, rather than a HOL declaration over unrestricted function maps. -/
def convertCodeRaw {width : Nat} [NeZero width] {κ : Type}
    (context : ContextExact)
    (code : κ → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (key : κ) : Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL) :=
  (code key).map fun payload =>
    (payload.1.map (fun parameter => (parameter.1, compileShapeExact context.structs parameter.2)),
      compileProgExact { context with locals := payload.1 } payload.2.1,
      compileShapeExact context.structs payload.2.2)

/-- Canonical-to-raw lookup correspondence without a relation premise. -/
theorem holFmapAsFiniteSupportResultWitness_convertCodeExact
    {width : Nat} [NeZero width] {κ : Type}
    (context : ContextExact)
    (code : Flapjack.HolFiniteMapExact κ (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (key : κ) :
    (convertCodeExact context code).lookup key = convertCodeRaw context code.lookup key := rfl
end Flapjack.Pancake.PanStructs.CompileShapeExact
