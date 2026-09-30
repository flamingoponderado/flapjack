import Flapjack.Pancake.PanStructs.CompileProgExact
import Flapjack.Pancake.PanLang.Decl

/-! Exact source declaration/top compilation. Source definitions alone do not
complete the executed production route, which remains separately tracked. -/
namespace Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.PanLang

@[hol "cakeml/pancake/pan_structsScript.sml" "compile_decs_def"
  (words_as_type_indexed_bitvec)]
def compileDeclsExact {width : Nat} [NeZero width]
    (context : ContextExact) : List (DeclHOL width) → List (DeclHOL width) × ContextExact
  | [] => ([], context)
  | .decl shape name value :: declarations =>
      let (compiled, finalContext) :=
        compileDeclsExact { context with globals := (name, shape) :: context.globals } declarations
      (.decl (compileShapeExact context.structs shape) name (compileExpExact context value) :: compiled,
        finalContext)
  | .function declaration :: declarations =>
      let (compiled, finalContext) := compileDeclsExact context declarations
      let parameters := declaration.params
      let function := { declaration with
        params := parameters.map fun p => (p.1, compileShapeExact context.structs p.2)
        body := compileProgExact { finalContext with locals := parameters } declaration.body
        returnShape := compileShapeExact context.structs declaration.returnShape }
      (.function function :: compiled, finalContext)
  | .name _ _ :: declarations => compileDeclsExact context declarations
  | .exnDecl name shape :: declarations =>
      let (compiled, finalContext) := compileDeclsExact context declarations
      (.exnDecl name (compileShapeExact context.structs shape) :: compiled, finalContext)

@[hol "cakeml/pancake/pan_structsScript.sml" "get_names_def"
  (words_as_type_indexed_bitvec)]
def getNamesExact {width : Nat} [NeZero width]
    (context : ContextExact) : List (DeclHOL width) → ContextExact
  | [] => context
  | .name name fields :: declarations =>
      getNamesExact { context with structs := (name, fields) :: context.structs } declarations
  | _ :: declarations => getNamesExact context declarations

@[hol "cakeml/pancake/pan_structsScript.sml" "compile_top_def"
  (words_as_type_indexed_bitvec)]
def compileTopExact {width : Nat} [NeZero width] (declarations : List (DeclHOL width)) :
    List (DeclHOL width) :=
  let initial : ContextExact := { structs := [], locals := [], globals := [] }
  (compileDeclsExact (getNamesExact initial declarations) declarations).1
end Flapjack.Pancake.PanStructs.CompileShapeExact
