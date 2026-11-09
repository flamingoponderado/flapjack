module

public import Flapjack.Compiler.Backend.ClosToBvl.Common
public import Flapjack.Compiler.Backend.ClosToBvl.SourceExps
public import Flapjack.Compiler.Backend.ClosToBvl.Names
public import Flapjack.Compiler.Backend.ClosToBvl.Sort
public import Flapjack.Compiler.Backend.ClosToBvl.Stubs

@[expose] public section

/-! Whole-program closure-to-BVL compilation in source order. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.Basis.Pure.MlString

/-- Compile the source closure program, add its stubs and retain its names. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "compile_def"]
noncomputable def compileSource (original : Config) (expressions : List ClosLang.Exp) :
    Config × List (Nat × Nat × Bvl.Exp) × Spt MlString :=
  let (current, program) := compileCommon original expressions
  let n := numStubs current.maxApp
  let initial := sptToAList (initCode current.maxApp)
  let initGlobalsProgram := [(n - 1, 0, initGlobals current.maxApp (n + current.start))]
  let forceProgram := [(n - 2, 2, forceThunkCode)]
  let compiled := compileProgExpsHOL current.maxApp program
  let all := initial ++ forceProgram ++ initGlobalsProgram ++ compiled
  let names := makeNameAlist (all.map Prod.fst) program n original.nextLoc expressions.length
  ({ current with start := n - 1 }, codeSort all, names)

end Flapjack.Compiler.Backend.ClosToBvl
