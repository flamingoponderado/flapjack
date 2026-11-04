import Flapjack.Parser
import Flapjack.Parser.ParseTopDecsByteRanged
import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.Pancake.Proofs.PanSimp.ProgOfHOL
import Flapjack.Pancake.PanGlobalsByteRanged
import Flapjack.Pancake.PanStructs.CompileExpCorrespondence
import Flapjack.Pancake.PanStructs.CompileDeclsExact
import Flapjack.CompileFunctionDistinct
import Flapjack.Pancake.CrepToLoop.ProductionCompileProg
import Flapjack.Pancake.PanToCrep.CompileToCrepBridge
import Flapjack.Pancake.CrepInline.InlineRouteNames
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

end Flapjack.Test.LoopToWordBoundaryParity
