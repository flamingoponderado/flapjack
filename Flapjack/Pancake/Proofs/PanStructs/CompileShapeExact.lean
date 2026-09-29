import Flapjack.HolRef
import Flapjack.Pancake.PanLang.Decl

/-!
Faithful carriers for the source `context` and mutually recursive
`compile_shape`/`compile_shapes` definitions in `pan_structsScript.sml`.
These are kept separate from the production `StructPassContext` and
`structCompileShapeWF`, whose String and cache-bearing structure carriers have
different types.
-/

namespace Flapjack.Pancake.Proofs.PanStructs.CompileShapeExact

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

/-- Exact HOL `pan_structs$context` (`pan_structsScript.sml:15-21`). The
    structure entries carry only field names and shapes; local/global entries
    carry variable names and shapes. -/
@[hol "cakeml/pancake/pan_structsScript.sml" "context" 16]
structure ContextExact where
  structs : List (MlS × List (MlS × ShapeHOL))
  locals : List (MlS × ShapeHOL)
  globals : List (MlS × ShapeHOL)

private theorem dropWhile_suffix_length_lt {α : Type} (p : α → Bool)
    (entries : List α) (head : α) (tail : List α)
    (hdrop : entries.dropWhile p = head :: tail) : tail.length < entries.length := by
  induction entries with
  | nil => simp at hdrop
  | cons entry entries ih =>
      by_cases hp : p entry = true
      · simp [List.dropWhile, hp] at hdrop
        have hlt := ih hdrop
        simp
        omega
      · simp [List.dropWhile, hp] at hdrop
        rcases hdrop with ⟨rfl, rfl⟩
        simp

/-! Exact source `compile_shape` (`pan_structsScript.sml:37-67`), over HOL's
    structure-list argument. The named case uses HOL's first-match
    `dropWhile (\(n,fs). ~(n = nm))`; a found entry compiles its field shapes
    in the suffix context. An absent name maps to `One`, as in the source's
    defensive fallback. -/
mutual
  @[hol "cakeml/pancake/pan_structsScript.sml" "compile_shape_def" 37]
  def compileShapeExact (context : List (MlS × List (MlS × ShapeHOL))) : ShapeHOL → ShapeHOL
    | .one => .one
    | .comb shapes => .comb (compileShapesExact context shapes)
    | .named name =>
        match _hdrop : context.dropWhile (fun entry => ! decide (entry.1 = name)) with
        | (_, fields) :: suffix => .comb (compileShapesExact suffix (fields.map Prod.snd))
        | [] => .one
  termination_by shape => (context.length, sizeOf shape)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | apply Prod.Lex.left
        exact dropWhile_suffix_length_lt
          (fun entry => ! decide (entry.1 = name)) context _ _ _hdrop
      | omega

  @[hol "cakeml/pancake/pan_structsScript.sml" "compile_shape_def" 37]
  def compileShapesExact (context : List (MlS × List (MlS × ShapeHOL))) : List ShapeHOL → List ShapeHOL
    | [] => []
    | shape :: shapes => compileShapeExact context shape :: compileShapesExact context shapes
  termination_by shapes => (context.length, sizeOf shapes)
  decreasing_by
    all_goals simp_wf
    all_goals try omega
    all_goals
      first
      | exact dropWhile_suffix_length_lt
          (fun entry => ! decide (entry.1 = name)) context _ _ _hdrop
      | omega
end

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
