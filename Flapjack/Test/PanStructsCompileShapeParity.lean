import Flapjack.Pancake.PanStructs
import Flapjack.Pancake.PanStructsByteRanged
import Flapjack.Pancake.Proofs.PanStructs
import Flapjack.Pancake.Proofs.PanStructs.CompileShapeExact
import Flapjack.Pancake.PanStructs.CompileShapeExact

namespace Flapjack.Test.PanStructsCompileShapeParity

open Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanStructs.CompileShapeExact
open Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Basis.Pure.MlString

private def byteRangedStructCompileInput : List (Decl (BitVec 8)) :=
  [ .name "Packet" [("field", .one)]
  , .decl (.named "Packet") "packet" (.const (7 : BitVec 8))
  , .function {
      name := "getField"
      inline := false
      exported := false
      params := [("value", .named "Packet")]
      body := .return (.nField "field" (.var .local "value"))
      returnShape := .one
    }
  ]

private theorem byteRangedStructCompileInput_ok :
    ∀ declaration ∈ byteRangedStructCompileInput, DeclByteRanged declaration := by
  intro declaration hmem
  simp [byteRangedStructCompileInput] at hmem
  rcases hmem with hmem | hmem | hmem
  · cases hmem
    simp [DeclByteRanged, NameRanged, ListParamByteRanged, ParamByteRanged, ShapeByteRanged]
  · cases hmem
    simp [DeclByteRanged, NameRanged, ShapeByteRanged, ExpByteRanged]
  · cases hmem
    simp [DeclByteRanged, FunDeclByteRanged, NameRanged, ListParamByteRanged,
      ParamByteRanged, ShapeByteRanged, ProgByteRanged, ExpByteRanged]

/-! Direct replay of the source HOL-EVAL rows in
    `scripts/hol-probes/compile_shape_probe.out` using the exact
    `MlString`/`ShapeHOL` carrier. -/
private def holOuter := ofString "outer"
private def holInner := ofString "inner"
private def holField := ofString "field"
private def holValue := ofString "value"

private def exactForwardContext : ContextExact :=
  { structs :=
      [(holOuter, [(holField, .named holInner)]),
       (holInner, [(holValue, .one)])]
    , locals := []
    , globals := [] }

private def exactBackwardContext : ContextExact :=
  { structs :=
      [(holInner, [(holValue, .one)]),
       (holOuter, [(holField, .named holInner)])]
    , locals := []
    , globals := [] }

private def exactCompileShapeOracleRows : Bool :=
  (match compileShapeExact exactForwardContext.structs .one with
   | .one => true | _ => false) &&
  (match compileShapeExact exactForwardContext.structs (.comb [.one, .one]) with
   | .comb [.one, .one] => true | _ => false) &&
  (match compileShapeExact exactForwardContext.structs (.named holOuter) with
   | .comb [.comb [.one]] => true | _ => false) &&
  (match compileShapeExact exactBackwardContext.structs (.named holOuter) with
   | .comb [.one] => true | _ => false) &&
  (match compileShapeExact exactForwardContext.structs (.named (ofString "missing")) with
   | .one => true | _ => false)

#eval exactCompileShapeOracleRows
#guard exactCompileShapeOracleRows

/-! Direct parity for `pan_structs$compile_shape_def`
    (`pan_structsScript.sml:37`).  The nested cases distinguish the source's
    suffix context from an incorrect lookup through the whole context. -/
def forwardContext : StructContext :=
  [("outer", { fields := [("field", .named "inner")], size := 1 }),
   ("inner", { fields := [("value", .one)], size := 1 })]

def backwardContext : StructContext :=
  [("inner", { fields := [("value", .one)], size := 1 }),
   ("outer", { fields := [("field", .named "inner")], size := 1 })]

def parityGuard : Bool :=
  (match structCompileShape forwardContext .one with
  | .one => true
  | _ => false) &&
  (match structCompileShape forwardContext (.comb [.one, .one]) with
  | .comb [.one, .one] => true
  | _ => false) &&
  (match structCompileShape forwardContext (.named "outer") with
  | .comb [.comb [.one]] => true
  | _ => false) &&
  (match structCompileShape backwardContext (.named "outer") with
  | .comb [.one] => true
  | _ => false) &&
  (match structCompileShape forwardContext (.named "missing") with
  | .one => true
  | _ => false)

#eval parityGuard
#guard parityGuard

/-! Exact no-fuel list fixture for the direct HOL-EVAL `compile_shapes_map`
    oracle. It exercises recursive named expansion through the production
    no-fuel mutually recursive helper. -/
theorem structCompileShapes_eq_map_fixture :
    structCompileShapeWF.structCompileShapesWF forwardContext
      [.named "outer", .comb [.one, .named "inner"], .named "missing"] =
      [.comb [.comb [.one]], .comb [.one, .comb [.one]], .one] := by
  rw [structCompileShapes_eq_map]
  simp [structCompileShapeWF, structCompileShapeWF.structCompileShapesWF,
    forwardContext, lookupInfoWithRest]

/-! Direct counterpart of the original HOL `is_wf_shape_compile_shape`
    oracle rows below. Check both the single-shape and mutually recursive list
    conclusions over an unrelated outer context. -/
def unrelatedOuterContext : StructContext :=
  [("unused", { fields := [], size := 0 })]

theorem structCompileShapeWF_isWfShape_fixture :
    isWfShape unrelatedOuterContext
        (structCompileShapeWF forwardContext (.named "outer")) = true ∧
      isWfShape.isWfShapeList unrelatedOuterContext
        (structCompileShapeWF.structCompileShapesWF forwardContext
          [.named "outer", .comb [.one, .named "inner"], .named "missing"]) = true := by
  have hshape := (structCompileShapeWF_isWfShape unrelatedOuterContext).1
    forwardContext (.named "outer")
  have hshapes := (structCompileShapeWF_isWfShape unrelatedOuterContext).2
    forwardContext [.named "outer", .comb [.one, .named "inner"], .named "missing"]
  exact ⟨hshape, hshapes⟩

/-! Paired concrete instance of HOL `size_of_compile_shape` from the
    `size_of_compile_shape_comb` oracle row. -/
def sizeOfCompileShapeParityGuard : Bool :=
  isWfShape ([] : StructContext) (.comb [.one, .one]) &&
    (shapeSizeWithContext []
      (structCompileShapeWF ([] : StructContext) (.comb [.one, .one])) == 2) &&
    (shapeSizeWithContext ([] : StructContext) (.comb [.one, .one]) == 2)

#eval sizeOfCompileShapeParityGuard
#guard sizeOfCompileShapeParityGuard

theorem structCompileShapeWF_size_comb_fixture :
    shapeSizeWithContext []
        (structCompileShapeWF ([] : StructContext) (.comb [.one, .one])) =
      shapeSizeWithContext ([] : StructContext) (.comb [.one, .one]) := by
  exact structCompileShapeWF_size [] (.comb [.one, .one])
    (by simp [isWfShape, isWfShape.isWfShapeList]) (by simp [structInfosOk])

/-! The fuel-indexed helper remains a separate untagged analogue. -/
theorem structCompileShapesFuel_eq_map_fixture :
    structCompileShapeFuel.structCompileShapesFuel 8 forwardContext
      [.named "outer", .comb [.one, .named "inner"], .named "missing"] =
      [.comb [.comb [.one]], .comb [.one, .comb [.one]], .one] := by
  rw [structCompileShapesFuel_eq_map]
  simp [structCompileShapeFuel, structCompileShapeFuel.structCompileShapesFuel,
    forwardContext, lookupInfoWithRest]

/-! Cake's `function_names_structs_compile_top`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:313`). -/

def namesFunction : FunDecl Nat :=
  { name := "f", inline := false, exported := false, params := [],
    body := (.skip : Prog Nat), returnShape := .one }

def namesDecls : List (Decl Nat) :=
  [.function namesFunction, .decl .one "g" (.const 1), .name "S" []]

end Flapjack.Test.PanStructsCompileShapeParity
