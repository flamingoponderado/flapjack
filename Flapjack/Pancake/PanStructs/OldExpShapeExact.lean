import Flapjack.Pancake.PanStructs.CompileShapeExact

/-! Exact expression-shape dependency of structure compilation. Production
routing through these definitions remains a separate obligation. -/
namespace Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.PanLang

mutual
  /-- First-match association-list lookup uses propositional identifier equality;
  indexed fields use optional list indexing with HOL's defensive One default. -/
  @[hol "cakeml/pancake/pan_structsScript.sml" "old_exp_shape_def"
    (words_as_type_indexed_bitvec)]
  def oldExpShapeExact {width : Nat} [NeZero width]
      (context : ContextExact) : ExpHOL width → ShapeHOL
    | .var .local name =>
        (context.locals.findSome? (fun p => if p.1 = name then some p.2 else none)).getD .one
    | .var .global name =>
        (context.globals.findSome? (fun p => if p.1 = name then some p.2 else none)).getD .one
    | .rstruct fields => .comb (oldExpShapesExact context fields)
    | .rfield index value =>
        match oldExpShapeExact context value with
        | .comb shapes => shapes[index]?.getD .one
        | _ => .one
    | .nstruct name _ => .named name
    | .nfield field value =>
        match oldExpShapeExact context value with
        | .named name =>
            match context.structs.findSome? (fun p => if p.1 = name then some p.2 else none) with
            | some fields =>
                (fields.findSome? (fun p => if p.1 = field then some p.2 else none)).getD .one
            | none => .one
        | _ => .one
    | .load shape _ => shape
    | _ => .one
  termination_by expression => sizeOf expression
  decreasing_by all_goals simp_wf; all_goals omega

  @[hol "cakeml/pancake/pan_structsScript.sml" "old_exp_shape_def"
    (words_as_type_indexed_bitvec)]
  def oldExpShapesExact {width : Nat} [NeZero width]
      (context : ContextExact) : List (ExpHOL width) → List ShapeHOL
    | [] => []
    | expression :: expressions =>
        oldExpShapeExact context expression :: oldExpShapesExact context expressions
  termination_by expressions => sizeOf expressions
  decreasing_by all_goals simp_wf; all_goals omega
end
end Flapjack.Pancake.PanStructs.CompileShapeExact
