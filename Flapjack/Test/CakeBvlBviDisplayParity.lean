import Flapjack.Compiler.Backend.PresLang.Bvi
import Flapjack.Compiler.Backend.ClosToBvl.Stubs
import Flapjack.Compiler.Backend.BvlToBvi.Stubs
import Flapjack.Compiler.Backend.BvlToBvi.Names

/-! The expected functions are the first BVL and BVI functions emitted by
the pinned CakeML compiler in the explorer regression program. -/
namespace Flapjack.Test.CakeBvlBviDisplayParity

open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend

private def bvlExpected : String :=
  "(func bvl_stub@31 (h g f e d c b a)\n" ++
  "   (let\n      (i <- (op (ElemAt 2) (var a)))\n" ++
  "      (call none (var h) (var g) (var f) (var e) (var d)\n" ++
  "         (var c) (var b) (op (ElemAt 3) (var a)) (var i)\n" ++
  "         (op (ElemAt 0) (var i)))))\n\n"

private def bvlStub : Option String := do
  let (arity, body) ← sptLookup 31 (ClosToBvl.initCode 10)
  let names := sptInsert 31 (ofString "bvl_stub") .ln
  pure (String.join (PresLang.Bvl.programs names [(31, arity, body)]))

private def bviExpected : String :=
  "(func AllocGlobal@62 (a)\n   (let\n      (b <- (op GlobalsPtr))\n" ++
  "      (let\n         (c <- (op El (op (Const 0)) (var b)))\n" ++
  "         (let\n            (d <- (op Add (var c) (var a)))\n" ++
  "            (let\n               (e <- (op Length (var b)))\n" ++
  "               (let\n                  (f <- (op Update (var d) (op (Const 0)) (var b)))\n" ++
  "                  (if (op Less (var e) (var d)) (var f)\n" ++
  "                     (let\n                        (g <- (op RefArray (op (Const 0)) (op Add (var d) (var d))))\n" ++
  "                        (let\n                           (h <- (op SetGlobalsPtr (var g)))\n" ++
  "                           (call CopyGlobals@63 (var g) (var b)\n" ++
  "                              (op Sub (op (Const 1)) (var e))))))))))))\n\n"

private def bviStub : String :=
  let names := sptInsert 62 (ofString "AllocGlobal") (sptInsert 63 (ofString "CopyGlobals") .ln)
  String.join (PresLang.Bvi.programs names [(62, BvlToBvi.allocGlobalCode.1, BvlToBvi.allocGlobalCode.2)])

private def bviStartExpected : String :=
  "(func start@64 ()\n   (let\n      (a <- (op RefArray (op (Const 0)) (op (Const 3))))\n" ++
  "      (let\n         (b <- (op Update (op (Const 1)) (op (Const 0)) (var a)))\n" ++
  "         (let\n            (c <- (op SetGlobalsPtr (var a)))\n" ++
  "            (call bvl_init@296 (handler d -> (var d)))))))\n\n"

private def bviStart : String :=
  let names := sptInsert 64 (ofString "start") (sptInsert 296 (ofString "bvl_init") .ln)
  let (_, code) := BvlToBvi.initGlobalsCode 296 3
  String.join (PresLang.Bvi.programs names [(64, 0, code)])

#guard bvlStub == some bvlExpected
#guard bviStub == bviExpected
#guard bviStart == bviStartExpected

end Flapjack.Test.CakeBvlBviDisplayParity
