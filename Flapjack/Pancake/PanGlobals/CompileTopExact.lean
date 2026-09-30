import Flapjack.Pancake.PanGlobals.CompileExpExact

namespace Flapjack

open Flapjack.Pancake.PanLang

/-- Local factoring of the top compiler's first-match function selection.
This helper has no independent CakeML declaration. -/
private def compileTopFunctionLookup {width : Nat} [NeZero width] (start : MlS) :
    List (MlS × List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL) →
    Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)
  | [] => none
  | (name, entry) :: entries =>
      if start = name then some entry else compileTopFunctionLookup start entries

/-- Literal exact-carrier top compiler. The internally created finite map is
the reviewed empty canonical map consumed by compileDecsExactHOL; the public
input/output contain no finite-map field. Executed top-level routing remains
separately tracked. -/
@[hol "cakeml/pancake/pan_globalsScript.sml" "compile_top_def"
  (words_as_type_indexed_bitvec)]
def compileTopExactHOL {width : Nat} [NeZero width]
    (declarations : List (DeclHOL width)) (start : MlS) : List (DeclHOL width) :=
  match compileTopFunctionLookup start (functionsHOL declarations) with
  | none => []
  | some (arguments, _body, returnShape) =>
      let resorted := resortDeclsHOL declarations
      let newStart := newMainNameHOL declarations
      let renamed := fpermDecsHOL start newStart resorted
      let initial : PanGlobalsContextExact width :=
        { globals := HolFiniteMapExact.empty
          globalsSize := 0
          maxGlobalsSize := cakeBytesInWord width * BitVec.ofNat width
            ((decShapesHOL renamed).map sizeOfShapeHOL).sum }
      let (initializers, functions, exceptions, _context) :=
        compileDecsExactHOL initial renamed
      let parameters := arguments.map (fun entry => ExpHOL.var .local entry.1)
      let newMain : DeclHOL width := .function
        { name := start
          inline := false
          exported := false
          params := arguments
          body := .seq (nestedSeqHOL initializers) (.call none newStart parameters)
          returnShape := returnShape }
      exceptions ++ newMain :: functions

end Flapjack
