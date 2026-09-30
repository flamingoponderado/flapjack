import Flapjack.Pancake.PanStructs.OldExpShapeExact
import Flapjack.Pancake.PanStructs

/-! Exact source expression compilation. Production expression routing is still
an open obligation; these definitions preserve the HOL context and syntax. -/
namespace Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.PanLang

mutual
  @[hol "cakeml/pancake/pan_structsScript.sml" "compile_exp_def"
    (words_as_type_indexed_bitvec)]
  def compileExpExact {width : Nat} [NeZero width]
      (context : ContextExact) : ExpHOL width → ExpHOL width
    | .rstruct fields => .rstruct (compileExpsExact context fields)
    | .rfield index value => .rfield index (compileExpExact context value)
    | .nstruct name fields =>
        let compiled := compileFieldsExact context fields
        let selected := match context.structs.findSome?
            (fun p => if p.1 = name then some p.2 else none) with
          | some fields => fields.flatMap fun p =>
              match compiled.findSome? (fun q => if q.1 = p.1 then some q.2 else none) with
              | none => []
              | some value => [value]
          | none => []
        .rstruct selected
    | .nfield field value =>
        let compiled := compileExpExact context value
        let index := match oldExpShapeExact context value with
          | .named name =>
              match context.structs.findSome?
                  (fun p => if p.1 = name then some p.2 else none) with
              | some fields => (Flapjack.afindi field fields).getD 0
              | none => 0
          | _ => 0
        .rfield index compiled
    | .load shape address =>
        .load (compileShapeExact context.structs shape) (compileExpExact context address)
    | .loadByte address => .loadByte (compileExpExact context address)
    | .load32 address => .load32 (compileExpExact context address)
    | .op operator args => .op operator (compileExpsExact context args)
    | .panop operator args => .panop operator (compileExpsExact context args)
    | .cmp operator left right =>
        .cmp operator (compileExpExact context left) (compileExpExact context right)
    | .shift operator left right =>
        .shift operator (compileExpExact context left) (compileExpExact context right)
    | expression => expression
  termination_by expression => sizeOf expression
  decreasing_by all_goals simp_wf; all_goals omega

  @[hol "cakeml/pancake/pan_structsScript.sml" "compile_exp_def"
    (words_as_type_indexed_bitvec)]
  def compileExpsExact {width : Nat} [NeZero width]
      (context : ContextExact) : List (ExpHOL width) → List (ExpHOL width)
    | [] => []
    | expression :: expressions =>
        compileExpExact context expression :: compileExpsExact context expressions
  termination_by expressions => sizeOf expressions
  decreasing_by all_goals simp_wf; all_goals omega

  @[hol "cakeml/pancake/pan_structsScript.sml" "compile_exp_def"
    (words_as_type_indexed_bitvec)]
  def compileFieldsExact {width : Nat} [NeZero width]
      (context : ContextExact) : List (MlS × ExpHOL width) → List (MlS × ExpHOL width)
    | [] => []
    | (name, expression) :: fields =>
        (name, compileExpExact context expression) :: compileFieldsExact context fields
  termination_by fields => sizeOf fields
  decreasing_by all_goals simp_wf; all_goals omega
end
end Flapjack.Pancake.PanStructs.CompileShapeExact
