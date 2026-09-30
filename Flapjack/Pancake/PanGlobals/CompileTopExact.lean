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

/-- The top compiler's first-match selection commutes with decoding exact
declarations and names. Only the arguments, body and return shape are selected
by HOL `compile_top`; inline/export flags are intentionally outside this
projection. This is Flapjack cross-carrier infrastructure with no independent
HOL declaration, and does not yet establish the complete top compiler route. -/
theorem compileTopFunctionLookup_decode {width : Nat} [NeZero width]
    (declarations : List (DeclHOL width)) (start : MlS) :
    (compileTopFunctionLookup start (functionsHOL declarations)).map
        (fun entry => (entry.1.map paramOfHOL, progOfHOL entry.2.1,
          shapeOfHOL entry.2.2)) =
      (globalFindFunction (Flapjack.Basis.Pure.MlString.toStringOfBytes start)
        (declarations.map declOfHOL)).map
          (fun entry => (entry.params, entry.body, entry.returnShape)) := by
  induction declarations with
  | nil => simp [functionsHOL, compileTopFunctionLookup, globalFindFunction]
  | cons declaration declarations ih =>
      cases declaration with
      | function entry =>
          by_cases h : start = entry.name
          · subst start
            simp [functionsHOL, compileTopFunctionLookup, globalFindFunction,
              declOfHOL, funDeclOfHOL]
          · have hdecoded :
                Flapjack.Basis.Pure.MlString.toStringOfBytes entry.name ≠
                  Flapjack.Basis.Pure.MlString.toStringOfBytes start := by
              intro heq
              exact h (toStringOfBytes_injective heq).symm
            simpa [functionsHOL, compileTopFunctionLookup, globalFindFunction,
              declOfHOL, funDeclOfHOL, h, hdecoded] using ih
      | decl shape name value =>
          simpa [functionsHOL, globalFindFunction, declOfHOL] using ih
      | exnDecl name shape =>
          simpa [functionsHOL, globalFindFunction, declOfHOL] using ih
      | name name shape =>
          simpa [functionsHOL, globalFindFunction, declOfHOL] using ih

/-- Literal exact-carrier top compiler. The internally created finite map is
the reviewed empty canonical map consumed by compileDecsExactHOL; the public
input/output contain no finite-map field. The parser-path production route
`globalCompileTopCakeRouted` (`Flapjack.Pancake.PanGlobalsByteRanged`) executes
this definition and decodes its output; `compileTopExactHOL_decode` proves that
equal to the compatibility `globalCompileTopCake`. -/
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
