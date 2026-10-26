import Flapjack.Compiler.Backend.FlatElim.Reachability
import Flapjack.Compiler.Backend.SourceToFlat.Eliminate
import Flapjack.Compiler.Backend.FlatPattern.Names
import Flapjack.Compiler.Backend.FlatPattern.Decode
import Flapjack.Compiler.Backend.FlatPattern.Encode
import Flapjack.Test.CakeMLFlatOracle

namespace Flapjack.Test.FlatElim
open Flapjack Flapjack.Compiler.Backend.FlatLang Flapjack.Compiler.Backend.FlatElim
open Flapjack.Basis.Pure.MlString

private def lit : Exp := .lit .none (.intLit 1)
private def get1 : Exp := .app .none (.globalVarLookup 1) []
private def set2 : Exp := .app .none (.globalVarInit 2) [get1]
private def eval : Exp := .app .none (.src .eval) []
open Flapjack.Test.CakeMLFlatOracle

-- An assignment containing a lookup is effectful and immediately reachable.
#guard isPure set2 == impure_lookup_init
#guard isHidden set2 == hidden_lookup_init
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
#guard isPure pureSet == pure_init
#guard isHidden pureSet == hidden_init
#guard keep .ln pureSet == keep_empty
#guard keep (sptInsert 2 () .ln) pureSet == keep_reachable
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
#guard (removeFlatProg [pureSet]).map List.length == some eliminate_pure_length
#guard (removeFlatProg [eval, pureSet]).map List.length == some eval_bypass_length
example : removeFlatProg [eval, pureSet] = some [eval, pureSet] := rfl
#guard ((Flapjack.Compiler.Backend.SourceToFlat.compileProgElim
  Flapjack.Compiler.Backend.SourceToFlat.emptyConfig []).map (fun result => result.2.length)) == some 2
#guard (Flapjack.Compiler.Backend.SourceToFlat.compileProg
  Flapjack.Compiler.Backend.SourceToFlat.emptyConfig []).1.next.vidx == empty_program_globals
#guard empty_program_output

-- Reserved pattern names round-trip at both sides of the encoding boundary.
#guard Flapjack.Compiler.Backend.FlatPattern.decNameToNum (ofString "x") == nameUnreserved
#guard [0, 89, 90, 181].map (fun n => Flapjack.Compiler.Backend.FlatPattern.decNameToNum
  (Flapjack.Compiler.Backend.FlatPattern.encNumToName n)) == nameRoundtrips
#guard [0, 89, 90, 181].map (fun n =>
  (Flapjack.Compiler.Backend.FlatPattern.encNumToName n).explode.map BitVec.toNat) == nameBytes

open Flapjack.Compiler.Backend.FlatPattern Flapjack.Compiler.Backend.PatternSemantics
#guard decide (simpGuard (.not (.not .true_)) = .true_) == guard_double_not
#guard decide (simpGuard (.conj .true_ (.not .true_)) = .not .true_) == guard_false_conj
example : decodeDtree .none .ln lit pureSet (.leaf 4) = pureSet := rfl
example : decodeDtree .none (.ls lit) lit pureSet (.leaf 0) = lit := rfl
example : decodeDtree .none .ln lit pureSet (.if_ .true_ (.leaf 0) .typeFail) = pureSet := rfl
example : encodePat (.pcon (some (3, some (42, [(3, 1)]))) [.pany]) =
    .cons (some (3, some [(3, 1)])) [.any] := rfl
#guard pattern_encoding

end Flapjack.Test.FlatElim
