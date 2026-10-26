import Flapjack.Compiler.Backend.FlatElim.Reachability
import Flapjack.Compiler.Backend.SourceToFlat.Eliminate
import Flapjack.Compiler.Backend.FlatPattern.Names

namespace Flapjack.Test.FlatElim
open Flapjack Flapjack.Compiler.Backend.FlatLang Flapjack.Compiler.Backend.FlatElim
open Flapjack.Basis.Pure.MlString

private def lit : Exp := .lit .none (.intLit 1)
private def get1 : Exp := .app .none (.globalVarLookup 1) []
private def set2 : Exp := .app .none (.globalVarInit 2) [get1]
private def eval : Exp := .app .none (.src .eval) []

-- An assignment containing a lookup is effectful and immediately reachable.
#guard !isPure set2 && !isHidden set2
#guard (sptLookup 2 (findLoc set2)).isSome
#guard (sptLookup 1 (findLookups set2)).isSome
#guard (sptLookup 2 (analyseExp set2).1).isSome
#guard (sptLookup 1 (analyseExp set2).1).isSome

-- Function bodies are hidden and pure, but still scanned for dependencies and Eval.
private def function : Exp := .fn (ofString "f") (ofString "x")
  (.let_ .none none set2 eval)
#guard isPure function && isHidden function && hasEval function
#guard (sptLookup 2 (findLoc function)).isSome
#guard (sptLookup 1 (findLookups function)).isSome

-- A pure assignment can be removed unless its location is reachable.
private def pureSet : Exp := .app .none (.globalVarInit 2) [lit]
#guard isPure pureSet && isHidden pureSet
#guard !keep .ln pureSet
#guard keep (sptInsert 2 () .ln) pureSet
#guard keep .ln eval

-- Only a match with a total pattern is considered pure.
#guard isPure (.mat .none lit [(.pany, lit)])
#guard !isPure (.mat .none lit [(.plit (.intLit 0), lit)])

-- A two-edge dependency chain needs successive closure iterations.
private def graph : Spt NumSet :=
  sptInsert 1 (sptInsert 2 () .ln) (sptInsert 2 (sptInsert 3 () .ln) .ln)
private def roots : NumSet := sptInsert 1 () .ln
#guard (closureFuel 2 roots graph).isNone
#guard ((closureFuel 3 roots graph).bind (sptLookup 3)).isSome
#guard (closureFuel 3 roots graph).isSome
#guard (removeFlatProgFuel 0 [eval]).isSome
#guard (removeFlatProgFuel 0 [pureSet]).isNone
#guard (removeFlatProg [pureSet]).map List.length == some 0
#guard (removeFlatProg [eval, pureSet]).map List.length == some 2
#guard ((Flapjack.Compiler.Backend.SourceToFlat.compileProgElim
  Flapjack.Compiler.Backend.SourceToFlat.emptyConfig []).map (fun result => result.2.length)) == some 2

-- Reserved pattern names round-trip at both sides of the encoding boundary.
#guard Flapjack.Compiler.Backend.FlatPattern.decNameToNum (ofString "x") == 0
#guard Flapjack.Compiler.Backend.FlatPattern.decNameToNum
  (Flapjack.Compiler.Backend.FlatPattern.encNumToName 89) == 89
#guard Flapjack.Compiler.Backend.FlatPattern.decNameToNum
  (Flapjack.Compiler.Backend.FlatPattern.encNumToName 90) == 90
#guard Flapjack.Compiler.Backend.FlatPattern.decNameToNum
  (Flapjack.Compiler.Backend.FlatPattern.encNumToName 181) == 181

end Flapjack.Test.FlatElim
