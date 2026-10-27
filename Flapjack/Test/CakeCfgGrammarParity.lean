import Flapjack.CakeParser.CfgGrammar
import Flapjack.CakeParser.CfgLocation
import Flapjack.CakeParser.Lexer
import Flapjack.CakeParser.PegEval

/-! Representative CFG productions from the pinned `cmlG_def` capture. -/
namespace Flapjack.Test.CakeCfgGrammarParity
open Flapjack.CakeParser Flapjack.CakeParser.CfgGrammar Flapjack.Misc.Grammar
open Flapjack.Basis.Pure.MlString

#guard (productions .nTopLevelDecs).any (fun p => matchesProduction p [])
#guard (productions .nTopLevelDecs).any (fun p => matchesProduction p
  [.nt (.inl .nDecl), .nt (.inl .nNonETopLevelDecs)])
#guard !(productions .nTopLevelDecs).any (fun p => matchesProduction p [.tok .valT])
#guard (productions .nV).any (fun p => matchesProduction p [.tok (.alphaT (ofString "value"))])
#guard !(productions .nV).any (fun p => matchesProduction p [.tok (.alphaT (ofString "before"))])
#guard (productions .nEliteral).any (fun p => matchesProduction p [.tok (.intT 3)])
#guard (productions .nUQTyOp).any (fun p => matchesProduction p [.tok (.alphaT (ofString ""))])

example : validPtree cmlGrammar (.node (.inl .nTopLevelDecs, ()) []) := by
  simp [validPtree, cmlGrammar, productions, matchesProduction]

private def pegTreeValid (source : String) : Bool :=
  match Lexer.lexFuel 10000 (ofString source).explode Flapjack.Misc.Location.defaultLoc with
  | none => false
  | some tokens =>
    match PegEval.eval 10000 (.nt (.inl .nTopLevelDecs) .id) tokens with
    | .success [tree] [] => CfgLocation.validLocatedTree tree
    | _ => false

#guard pegTreeValid ""
#guard pegTreeValid "val x = 1;"
#guard pegTreeValid "fun id x = x; val z = id (1,2);"
#guard pegTreeValid "datatype t = A | B int; val x = B 2;"
#guard pegTreeValid "structure M = struct val x = 1; end; val y = M.x;"
#guard pegTreeValid "val z = case [1] of [] => 0 | x::xs => x;"

end Flapjack.Test.CakeCfgGrammarParity
