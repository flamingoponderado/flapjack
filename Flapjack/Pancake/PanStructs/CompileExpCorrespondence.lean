import Flapjack.Pancake.PanStructsByteRanged
import Flapjack.Pancake.PanStructs.CompileExpExact

/-! Flapjack codec infrastructure for this pass, with no HOL theorem original.
Correspondence requires the actual parser byte-range invariants rather than
assuming the compiler result or its simulation. -/
namespace Flapjack
open Pancake.PanLang Basis.Pure.MlString

/-- Flapjack factoring of the reviewed recursive expression-list compiler. -/
theorem compileExpsExact_eq_map {width : Nat} [NeZero width]
    (context : Pancake.PanStructs.CompileShapeExact.ContextExact)
    (expressions : List (ExpHOL width)) :
    Pancake.PanStructs.CompileShapeExact.compileExpsExact context expressions =
      expressions.map (Pancake.PanStructs.CompileShapeExact.compileExpExact context) := by
  induction expressions with
  | nil => simp [Pancake.PanStructs.CompileShapeExact.compileExpsExact]
  | cons expression expressions ih =>
      simp [Pancake.PanStructs.CompileShapeExact.compileExpsExact, ih]

/-- Flapjack factoring: field compilation preserves every supplied key and
its order, including duplicates; only expression payloads are compiled. -/
theorem compileFieldsExact_eq_map {width : Nat} [NeZero width]
    (context : Pancake.PanStructs.CompileShapeExact.ContextExact)
    (fields : List (MlS × ExpHOL width)) :
    Pancake.PanStructs.CompileShapeExact.compileFieldsExact context fields =
      fields.map (fun p =>
        (p.1, Pancake.PanStructs.CompileShapeExact.compileExpExact context p.2)) := by
  induction fields with
  | nil => simp [Pancake.PanStructs.CompileShapeExact.compileFieldsExact]
  | cons field fields ih =>
      rcases field with ⟨name, expression⟩
      simp [Pancake.PanStructs.CompileShapeExact.compileFieldsExact, ih]

/-- Flapjack shape codec fact used by the Load expression case. -/
theorem compileShapeExact_encode (context : StructContext) (shape : Shape)
    (hc : CtxBR context) (hs : ShapeByteRanged shape) :
    Pancake.PanStructs.CompileShapeExact.compileShapeExact
        (structContextToCompileShapeExact context) (shapeToHOL shape) =
      shapeToHOL (structCompileShape context shape) := by
  have h := congrArg shapeToHOL (structCompileShapeWF_eq_compileShapeExact context shape hc hs)
  simpa only [shapeToHOL_shapeOfHOL, structCompileShape] using h.symm

end Flapjack
