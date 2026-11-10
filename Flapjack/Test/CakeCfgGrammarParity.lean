module

public import Flapjack.CakeParser.CfgGrammar
public import Flapjack.CakeParser.CfgLocation
public import Flapjack.CakeParser.Lexer
public import Flapjack.CakeParser.PegEval

-- Checks below run compiled code from these modules.
public meta import Flapjack.Basis.Pure.MlString
public meta import Flapjack.CakeParser.CfgGrammar
public meta import Flapjack.CakeParser.CfgLocation
public meta import Flapjack.CakeParser.Lexer
public meta import Flapjack.CakeParser.PegEval
public meta import Flapjack.CakeParser.Tokens
public meta import Flapjack.Compiler.Backend.SourceToFlat.FromText
@[expose] public section

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
