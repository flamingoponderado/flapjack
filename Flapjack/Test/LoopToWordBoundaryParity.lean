module

public import Flapjack.Parser
public import Flapjack.Parser.ParseTopDecsByteRanged
public import Flapjack.Pancake.PanToCrep.Compile
public import Flapjack.Pancake.Proofs.PanSimp.ProgOfHOL
public import Flapjack.Pancake.PanGlobalsByteRanged
public import Flapjack.Pancake.PanStructs.CompileExpCorrespondence
public import Flapjack.Pancake.PanStructs.CompileDeclsExact
public import Flapjack.CompileFunctionDistinct
public import Flapjack.Pancake.CrepToLoop.ProductionCompileProg
public import Flapjack.Pancake.PanToCrep.CompileToCrepBridge
public import Flapjack.Pancake.CrepInline.InlineRouteNames
public import Flapjack.Pancake.LoopToWord
public import Flapjack.Pancake.LoopToWord.CompFuncExact
public import Flapjack.Pancake.LoopToWord.LoopProgCarrierCodec
public import Flapjack.RiscV.Allocator
public import Flapjack.RiscV.WordDiagnostics
public import Flapjack.RiscV.WordFuseConditions
public import Flapjack.RiscV.WordUnreach
public import Flapjack.RiscV.Lab
public import Flapjack.Display

-- Checks below run compiled code from these modules.
public meta import Flapjack.CompileFunctionDistinct
public meta import Flapjack.Display
public meta import Flapjack.Pancake.CrepInline.InlineRouteNames
public meta import Flapjack.Pancake.CrepToLoop.ProductionCompileProg
public meta import Flapjack.Pancake.LoopToWord
public meta import Flapjack.Pancake.LoopToWord.CompFuncExact
public meta import Flapjack.Pancake.LoopToWord.LoopProgCarrierCodec
public meta import Flapjack.Pancake.PanGlobalsByteRanged
public meta import Flapjack.Pancake.PanStructs.CompileDeclsExact
public meta import Flapjack.Pancake.PanStructs.CompileExpCorrespondence
public meta import Flapjack.Pancake.PanToCrep.Compile
public meta import Flapjack.Pancake.PanToCrep.CompileToCrepBridge
public meta import Flapjack.Pancake.Proofs.PanSimp.ProgOfHOL
public meta import Flapjack.Parser
public meta import Flapjack.Parser.ParseTopDecsByteRanged
public meta import Flapjack.RiscV.Allocator
public meta import Flapjack.RiscV.Lab
public meta import Flapjack.RiscV.WordDiagnostics
public meta import Flapjack.RiscV.WordFuseConditions
public meta import Flapjack.RiscV.WordUnreach
@[expose] public section

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

end Flapjack.Test.LoopToWordBoundaryParity
