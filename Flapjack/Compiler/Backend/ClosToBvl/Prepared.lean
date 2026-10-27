import Flapjack.Compiler.Backend.ClosToBvl.Config
import Flapjack.Compiler.Backend.ClosToBvl.Compile
import Flapjack.Compiler.Backend.ClosToBvl.Names
import Flapjack.Compiler.Backend.ClosToBvl.Sort
import Flapjack.Compiler.Backend.ClosToBvl.Stubs

/-! Checked closure-to-BVL assembly after closure preprocessing. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.Basis.Pure.MlString

/-- Assemble a prepared closure program with its application, force and
initialization stubs. The caller supplies the result of HOL's `compile_common`;
that preprocessing and the success of checked expression lowering remain
unproved, so this is not the full HOL `compile` definition. -/
def compilePrepared? (original current : Config) (es : List ClosLang.Exp)
    (prog : List (Nat × Nat × ClosLang.Exp)) :
    Option (Config × List (Nat × Nat × Bvl.Exp) × Spt MlString) := do
  let n := numStubs current.maxApp
  let initial := (sptToAList (initCode current.maxApp)).map fun (loc, arity, code) => (loc, arity, code)
  let compiled ← compileProg? current.maxApp prog
  let all := initial ++ [(n - 2, 2, forceThunkCode), (n - 1, 0, initGlobals current.maxApp (n + current.start))] ++ compiled
  let names := makeNameAlist (all.map (fun (loc, _, _) => loc)) prog n original.nextLoc es.length
  pure ({ current with start := n - 1 }, codeSort all, names)

end Flapjack.Compiler.Backend.ClosToBvl
