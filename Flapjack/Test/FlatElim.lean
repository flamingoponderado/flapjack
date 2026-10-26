import Flapjack.Compiler.Backend.FlatElim.Reachability
import Flapjack.Compiler.Backend.SourceToFlat.Eliminate
import Flapjack.Compiler.Backend.SourceToFlat.ToClos
import Flapjack.Compiler.Backend.ClosToBvl.Constants
import Flapjack.Compiler.Backend.ClosToBvl.Layout
import Flapjack.Compiler.Backend.ClosToBvl.Sort
import Flapjack.Compiler.Backend.FlatPattern.Names
import Flapjack.Compiler.Backend.FlatPattern.Decode
import Flapjack.Compiler.Backend.FlatPattern.Encode
import Flapjack.Compiler.Backend.FlatPattern.Bindings
import Flapjack.Compiler.Backend.FlatPattern.Patterns
import Flapjack.Compiler.Backend.PatternComp.Decision
import Flapjack.Compiler.Backend.PatternExh.Matrix
import Flapjack.Compiler.Backend.FlatToClos.Helpers
import Flapjack.Compiler.Backend.FlatToClos.Arith
import Flapjack.Compiler.Backend.FlatToClos.CopyByte
import Flapjack.Compiler.Backend.FlatToClos.Op
import Flapjack.Compiler.Backend.FlatToClos.Compile
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

open Flapjack.Compiler.Backend.FlatToClos
example : compileLit .none (.word8 255) = .op .none (.intOp (.const 255)) [] := rfl
#guard word8_literal
example : smartCons .none 4 [.op .none (.intOp (.const 1)) [],
    .op .none (.intOp (.const 2)) []] =
    .op .none (.blockOp (.constant (.constCons 4 [.constInt 2, .constInt 1]))) [] := rfl
#guard smart_constructor
example : compileArith .none .div .intT [] = .let .none []
    (.ifThenElse .none (.op .none (.blockOp .equal)
      [.var .none 0, .op .none (.intOp (.const 0)) []])
      (.raise .none (.op .none (.blockOp (.cons 2)) []))
      (.op .none (.intOp .div) [.var .none 0, .var .none 1])) := rfl
#guard int_division
example : copyByteStr .none =
  .ifThenElse .none (.op .none (.intOp .less) [.op .none (.intOp (.const 0)) [], .var .none 0])
    (.raise .none (.op .none (.blockOp (.cons 3)) []))
    (.ifThenElse .none (.op .none (.intOp .less) [.op .none (.intOp (.const 0)) [], .var .none 1])
      (.raise .none (.op .none (.blockOp (.cons 3)) []))
      (.ifThenElse .none (.op .none (.memOp (.boundsCheckByte true))
        [.op .none (.intOp .add) [.var .none 0, .var .none 1], .var .none 2])
        (.op .none (.memOp (.copyByte true)) [.var .none 0, .var .none 1, .var .none 2])
        (.raise .none (.op .none (.blockOp (.cons 3)) [])))) := rfl
#guard copy_string
example : compileOp .none (.src .aupdate) [] = .let .none []
    (.ifThenElse .none (.op .none (.memOp .boundsCheckArray) [.var .none 1, .var .none 2])
      (.op .none (.memOp .update) [.var .none 0, .var .none 1, .var .none 2])
      (.raise .none (.op .none (.blockOp (.cons 3)) []))) := rfl
example : compileOp .none (.src (.fromTo .intT (.wordT .w8))) [.var .none 7] =
    .op .none (.intOp .mod) [.op .none (.intOp (.const 256)) [], .var .none 7] := rfl
#guard array_update && word8_conversion
example : Flapjack.Compiler.Backend.FlatToClos.compile []
    [.let_ .none (some (ofString "x")) (.lit .none (.intLit 4))
      (.varLocal .none (ofString "x"))] =
    [.let .none [.op .none (.intOp (.const 4)) []] (.var .none 0)] := rfl
example : Flapjack.Compiler.Backend.FlatToClos.compile []
    [.con .none (some (4, none)) [.lit .none (.intLit 1), .lit .none (.intLit 2)]] =
    [.op .none (.blockOp (.constant (.constCons 4 [.constInt 1, .constInt 2]))) []] := rfl
#guard compile_let && compile_constructor
example : destNop (.src (.fromTo .intT (.wordT .w8)))
    [.app .none (.src (.fromTo .charT .intT)) [lit]] = some lit := rfl
example : Flapjack.Compiler.Backend.FlatToClos.compile []
    [.app .none (.src (.fromTo .intT (.wordT .w8)))
      [.app .none (.src (.fromTo .charT .intT)) [lit]]] =
    [.op .none (.intOp (.const 1)) []] := rfl
#guard compile_nop
example : Flapjack.Compiler.Backend.FlatToClos.compileProg [] =
    [Flapjack.Compiler.Backend.ClosInterp.compileInit false] := rfl
#guard closure_empty_program
#guard Flapjack.Compiler.Backend.ClosLang.hasInstallList
  [.fn (ofString "f") none none 1 (.op .none .install [])] == closure_install_detect
example : Flapjack.Compiler.Backend.ClosInterp.compileInit false =
    .let .none [.op .none (.globOp .allocGlobal) [.op .none (.intOp (.const 1)) []],
      .op .none (.blockOp (.cons 0)) []]
      (.op .none (.globOp (.setGlobal 0)) [.var .none 1]) := rfl
#guard closure_init_false
example : (Flapjack.Compiler.Backend.FlatToClos.incCompileDecs [] :
    List Flapjack.Compiler.Backend.ClosLang.Exp × List Nat) =
    ([.op .none (.blockOp (.cons 0)) []], []) := rfl
#guard incremental_empty
#guard [Flapjack.Compiler.Backend.ClosInterp.canInterpretOp (.blockOp (.cons 3)) 1,
  Flapjack.Compiler.Backend.ClosInterp.canInterpretOp (.blockOp (.cons 2)) 1] == interpreter_arity
example : Flapjack.Compiler.Backend.PatternComp.patsToCode
    [(.any, 4), (.lit (.intLit 3), 5)] = .leaf 4 := rfl
example : Flapjack.Compiler.Backend.PatternComp.patToGuard []
    (.cons (some (2, none)) [.lit (.intLit 7)]) =
    .conj (.posTest .emptyPos (.tagLenEq 2 1))
      (.posTest (.pos 0 .emptyPos) (.litEq (.intLit 7))) := rfl
#guard pattern_any_tree && pattern_constructor_guard
example : Flapjack.Compiler.Backend.PatternExh.ctorNub [.tagC 1 0, .refC, .tagC 1 0] =
    [.refC, .tagC 1 0] := rfl
example : Flapjack.Compiler.Backend.PatternExh.specRow (.tagC 2 1)
    [.any, .lit (.intLit 3)] = [[.any, .lit (.intLit 3)]] := rfl
#guard pattern_nub && pattern_specialize
example : Flapjack.Compiler.Backend.PatternComp.compFuel 1 [] = some .fail := rfl
example : Flapjack.Compiler.Backend.PatternComp.compFuel 3 [(.any, 7)] = some (.leaf 7) := rfl
example : Flapjack.Compiler.Backend.PatternComp.compFuel 0 [(.any, 7)] = none := rfl
#guard pattern_compile_empty && pattern_compile_any
example : compilePatRhsFuel 1 .none 0 (.varLocal .none (ofString "v"))
    (.pvar (ofString "x"), lit) =
    some (.let_ .none (some (ofString "x")) (.varLocal .none (ofString "v")) lit) := rfl
example : (compilePatRhsFuel 0 .none 0 (.varLocal .none (ofString "v"))
    (.pvar (ofString "x"), lit)).isNone = true := rfl
#guard pattern_bind_variable
#guard match compilePatsFuel 4 (Flapjack.Compiler.Backend.FlatPattern.initConfig 0) false
    .none 0 (.varLocal .none (ofString "v")) (.lit .none (.intLit 0))
    [(.pvar (ofString "x"), lit)] with
  | some (.let_ .none (some x) (.varLocal .none v) (.lit .none (.intLit 1))) =>
      x == ofString "x" && v == ofString "v"
  | _ => false
#guard pattern_compile_branch
#guard match compilePatsFuel 30 (Flapjack.Compiler.Backend.FlatPattern.initConfig 0) false
    .none 0 (.varLocal .none (ofString "v")) (.lit .none (.intLit 0))
    [(.pcon (some (2, none)) [.pvar (ofString "x")], .varLocal .none (ofString "x"))] with
  | some (.if_ .none (.app .none (.tagLenEq 2 1) [.varLocal .none v])
      (.let_ .none (some temp) (.app .none (.el 0) [.varLocal .none v'])
        (.let_ .none (some x) (.varLocal .none temp') (.varLocal .none x')))
      (.lit .none (.intLit 0))) =>
      v == ofString "v" && v' == ofString "v" && temp == ofString "..%" && temp' == temp &&
        x == ofString "x" && x' == x
  | _ => false
#guard pattern_constructor_branch
#guard match Flapjack.Compiler.Backend.SourceToFlat.compileToClosFuel 100
    Flapjack.Compiler.Backend.SourceToFlat.emptyConfig [] with
  | some (_, [
      .let .none [.op .none (.globOp .allocGlobal) [.op .none (.intOp (.const 1)) []],
        .op .none (.blockOp (.cons 0)) []] (.op .none (.globOp (.setGlobal 0)) [.var .none 1]),
      .let (.cons (.sourceLoc 2 2 1 1) 1)
        [.let (.cons (.sourceLoc 2 2 1 1) 1) []
          (.op (.cons (.sourceLoc 2 2 1 1) 1) (.globOp .allocGlobal)
            [.op (.cons (.sourceLoc 2 2 1 1) 1) (.intOp (.const 1)) []])]
        (.op (.cons (.sourceLoc 2 2 1 1) 1) (.blockOp (.cons 0)) []),
      .op .none (.globOp (.setGlobal 1)) [.op .none (.memOp .ref) [.op .none (.blockOp (.cons 0)) []]]]) => true
  | _ => false
#guard empty_source_to_clos
private def referenceOutput (result : Option (Flapjack.Compiler.Backend.SourceToFlat.Config ×
    List Flapjack.Compiler.Backend.ClosLang.Exp)) : Bool :=
  match result with
  | some (_, [
      .let .none [.op .none (.globOp .allocGlobal) [.op .none (.intOp (.const 1)) []],
        .op .none (.blockOp (.cons 0)) []] (.op .none (.globOp (.setGlobal 0)) [.var .none 1]),
      .let (.cons (.sourceLoc 2 2 1 1) 1)
        [.let (.cons (.sourceLoc 2 2 1 1) 1) []
          (.op (.cons (.sourceLoc 2 2 1 1) 1) (.globOp .allocGlobal)
            [.op (.cons (.sourceLoc 2 2 1 1) 1) (.intOp (.const 2)) []])]
        (.op (.cons (.sourceLoc 2 2 1 1) 1) (.blockOp (.cons 0)) []),
      .op .none (.globOp (.setGlobal 1)) [.op .none (.memOp .ref) [.op .none (.blockOp (.cons 0)) []]],
      .let .none [.op .none (.memOp .ref) [.op .none (.intOp (.const 1)) []]]
        (.let .none [.var .none 0] (.op .none (.globOp (.setGlobal 2)) [.var .none 0]))]) => true
  | _ => false
#guard referenceOutput (Flapjack.Compiler.Backend.SourceToFlat.compileToClosFuel 100
    Flapjack.Compiler.Backend.SourceToFlat.emptyConfig
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "x")) (.app .opref [.lit (.intLit 1)])])
#guard reference_source_to_clos
example : Flapjack.Compiler.Backend.SourceToSource.compile
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "x"))
      (.let_ (some (ofString "y")) (.lit (.intLit 1)) (.var (.short (ofString "y"))))] =
    [.dlocal [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "y")) (.lit (.intLit 1))]
      [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "x")) (.var (.short (ofString "y")))]] := by
  simp [Flapjack.Compiler.Backend.SourceToSource.compile, Flapjack.Compiler.Backend.SourceLet.compileDecs,
    Flapjack.Compiler.Backend.SourceLet.liftLets]
#guard source_let_lifting
#guard referenceOutput (Flapjack.Compiler.Backend.SourceToFlat.compileCakeToClosFuel 100
    Flapjack.Compiler.Backend.SourceToFlat.emptyConfig
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "x"))
      (.let_ (some (ofString "y")) (.app .opref [.lit (.intLit 1)]) (.var (.short (ofString "y"))))])
#guard lifted_source_to_clos
#guard match Flapjack.Compiler.Backend.SourceToFlat.compileCakeToClosFuel 100
    Flapjack.Compiler.Backend.SourceToFlat.emptyConfig
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "x"))
      (.app .opref [.mat (.lit (.intLit 1))
        [(.plit (.intLit 1), .lit (.intLit 2)), (.pany, .lit (.intLit 3))]])] with
  | some (_, [
      .let .none [.op .none (.globOp .allocGlobal) [.op .none (.intOp (.const 1)) []],
        .op .none (.blockOp (.cons 0)) []] (.op .none (.globOp (.setGlobal 0)) [.var .none 1]),
      .let (.cons (.sourceLoc 2 2 1 1) 1)
        [.let (.cons (.sourceLoc 2 2 1 1) 1) []
          (.op (.cons (.sourceLoc 2 2 1 1) 1) (.globOp .allocGlobal)
            [.op (.cons (.sourceLoc 2 2 1 1) 1) (.intOp (.const 2)) []])]
        (.op (.cons (.sourceLoc 2 2 1 1) 1) (.blockOp (.cons 0)) []),
      .op .none (.globOp (.setGlobal 1)) [.op .none (.memOp .ref) [.op .none (.blockOp (.cons 0)) []]],
      .let .none [.op .none (.memOp .ref) [
        .let .none [.op .none (.intOp (.const 1)) []]
          (.ifThenElse .none (.op .none (.blockOp .equal) [.op .none (.intOp (.const 1)) [], .var .none 0])
            (.op .none (.intOp (.const 2)) []) (.op .none (.intOp (.const 3)) []))]]
        (.let .none [.var .none 0] (.op .none (.globOp (.setGlobal 2)) [.var .none 0]))]) => true
  | _ => false
#guard match_source_to_clos
#guard match Flapjack.Compiler.Backend.ClosToBvl.compileConst
    (.constCons 30 [.constInt 1, .constInt 1]) with
  | .blockOp (.build [.int 1, .con 32 [0, 0]]) => true
  | _ => false
#guard bvl_shared_constant
#guard [Flapjack.Compiler.Backend.ClosToBvl.numStubs 4,
  Flapjack.Compiler.Backend.ClosToBvl.partialAppFnLocation 4 3 1] == bvl_stub_layout
example : Flapjack.Compiler.Backend.ClosToBvl.chainExps 7 [] =
    [(7, 0, .op .none (.intOp (.const 0)) [])] := rfl
#guard bvl_chain_empty
#guard Flapjack.Compiler.Backend.ClosToBvl.codeSort [(1, 10), (1, 20), (1, 30), (0, 40)] ==
  [(0, 40), (1, 20), (1, 30), (1, 10)]
#guard bvl_code_sort
example : Flapjack.Compiler.Backend.ClosToBvl.buildAux 3 [(1, .var 0), (2, .var 1)] [] =
    (7, [(5, 2, .var 1), (3, 1, .var 0)]) := rfl
#guard bvl_build_aux

end Flapjack.Test.FlatElim
