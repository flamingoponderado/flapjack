import Flapjack.Parser
import Flapjack.Parser.ParseTopDecsByteRanged
import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.Pancake.PanSimp.DeclsProduction
import Flapjack.Pancake.PanGlobalsByteRanged
import Flapjack.Pancake.PanStructs.CompileTopProduction
import Flapjack.Pancake.PanSimpByteRanged
import Flapjack.CompileFunctionDistinct
import Flapjack.Pancake.CrepToLoop.Optimise
import Flapjack.Pancake.CrepToLoop.ProductionDeclarations
import Flapjack.Pancake.LoopToWord
import Flapjack.Pancake.LoopToWord.CompFuncExact
import Flapjack.Pancake.LoopToWord.LoopProgCarrierCodec
import Flapjack.RiscV.Allocator
import Flapjack.RiscV.WordDiagnostics
import Flapjack.RiscV.WordFuseConditions
import Flapjack.RiscV.WordUnreach
import Flapjack.RiscV.Lab
import Flapjack.Display

namespace Flapjack.Test.LoopToWordBoundaryParity

open Flapjack Flapjack.LoopToWord

/-- `p1` fixture: identity plus a main with one dead call result. -/
def p1Source : String :=
  "fun 1 id (1 x) { return x; }
fun 1 main() { var 1 t = id(5); return 1; }"

/- `p9` is the smallest accepted struct witness with two distinct values live
   across two calls.  Cake's loop-to-word output has call cutsets `[0]` for
   `mks` and `[0,4,8]` for the later `id` call after dense renaming. -/
def p9Source : String :=
  "struct S { 1 f, 1 g }\n" ++
    "fun S mks (1 a, 1 b) { return S <f = a, g = b>; }\n" ++
    "fun 1 id (1 a) { return a; }\n" ++
    "fun 1 main() { var S s = mks(1,2); var 1 t = id(5); " ++
      "return s.f + s.g; }"

/-! `make_vmap_def` oracle: parameter names receive their dense positional
    slots and no entries are invented for an empty list.  Cake's `FEMPTY |++`
    is a left fold, so the executed list-backed map replays the pairs
    most-recent-first (reversed); lookups are unchanged. -/
def sourceMakeVmapOracle : Bool :=
  crepMakeVmap [] == [] &&
  crepMakeVmap [10, 20, 30] == [(30, 2), (20, 1), (10, 0)] &&
  lookupNatInfo 10 (crepMakeVmap [10, 20, 30]) == some 0 &&
  lookupNatInfo 30 (crepMakeVmap [10, 20, 30]) == some 2

#guard sourceMakeVmapOracle

/-! `comp_func_def` must resolve a source parameter through `make_vmap` before
    lowering.  This representative assignment is the source-to-Loop oracle:
    Cake's parameter name `10` is compiled to dense local slot `0`. -/
def sourceCompFuncOracle : Bool :=
  match crepCompFunc .rv64i [] [10] (.return [.var 10] : CrepProg Nat) with
  | .mark (.seq (.mark (.assign 1 (.var 0))) _) => true
  | _ => false

#guard sourceCompFuncOracle

/-! `mk_ctxt_def` field-order oracle: the constructor preserves both the
    source-name lookup map and Cake's fresh-variable bound. -/
def sourceMkCtxtOracle : Bool :=
  let context := crepMkCtxt (α := Nat) .rv64i (crepMakeVmap [10, 20])
    [("f", (64, 2))] 1
  context.vars == [(20, 1), (10, 0)] &&
    findLoopVar context 20 == 1 && context.maxVar == 1 &&
    context.functions == [("f", (64, 2))] &&
    match context.target with
    | .rv64i => true
    | _ => false

#guard sourceMkCtxtOracle

end Flapjack.Test.LoopToWordBoundaryParity
