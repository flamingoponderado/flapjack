import Flapjack.CakeParser.CfgGrammar

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
  simp [validPtree, cmlGrammar, Flapjack.HolFiniteMapExact.updateListEq,
    Flapjack.FUPDATE_LIST_HOL, Flapjack.FUPDATE_HOL, productions, nonterminals, matchesProduction]

end Flapjack.Test.CakeCfgGrammarParity
