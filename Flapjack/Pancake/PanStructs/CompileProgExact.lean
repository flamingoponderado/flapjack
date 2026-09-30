import Flapjack.Pancake.PanStructs.CompileExpExact
import Flapjack.Pancake.PanLang.Prog

/-! Exact source program compilation. Executed routing remains a separate
obligation. Declaration bodies bind the original source shape in the context;
only the emitted declaration shape is compiled. -/
namespace Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.PanLang

@[hol "cakeml/pancake/pan_structsScript.sml" "compile_def"
  (words_as_type_indexed_bitvec)]
def compileProgExact {width : Nat} [NeZero width]
    (context : ContextExact) : ProgHOL width → ProgHOL width
  | .dec name shape value body =>
      .dec name (compileShapeExact context.structs shape) (compileExpExact context value)
        (compileProgExact { context with locals := (name, shape) :: context.locals } body)
  | .assign kind name value => .assign kind name (compileExpExact context value)
  | .primitive name operator args => .primitive name operator (compileExpsExact context args)
  | .store address value => .store (compileExpExact context address) (compileExpExact context value)
  | .store32 address value => .store32 (compileExpExact context address) (compileExpExact context value)
  | .storeByte address value => .storeByte (compileExpExact context address) (compileExpExact context value)
  | .seq first second => .seq (compileProgExact context first) (compileProgExact context second)
  | .ite condition first second =>
      .ite (compileExpExact context condition) (compileProgExact context first) (compileProgExact context second)
  | .while condition body => .while (compileExpExact context condition) (compileProgExact context body)
  | .call info name args =>
      let compiled := compileExpsExact context args
      match info with
      | none => .call none name compiled
      | some (target, handler) =>
          .call (some (target, match handler with
            | none => none
            | some (exception, nameBound, body) =>
                some (exception, nameBound, compileProgExact context body))) name compiled
  | .decCall name shape function args body =>
      .decCall name (compileShapeExact context.structs shape) function (compileExpsExact context args)
        (compileProgExact { context with locals := (name, shape) :: context.locals } body)
  | .extCall name configuration configurationLength array arrayLength =>
      .extCall name (compileExpExact context configuration) (compileExpExact context configurationLength)
        (compileExpExact context array) (compileExpExact context arrayLength)
  | .return value => .return (compileExpExact context value)
  | .raise exception value => .raise exception (compileExpExact context value)
  | .shMemStore size first second =>
      .shMemStore size (compileExpExact context first) (compileExpExact context second)
  | .shMemLoad size kind name address => .shMemLoad size kind name (compileExpExact context address)
  | program => program
termination_by program => sizeOf program
decreasing_by all_goals simp_wf; all_goals omega
end Flapjack.Pancake.PanStructs.CompileShapeExact
