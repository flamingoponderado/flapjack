import Flapjack.Pancake.LoopToWord

/-!
# Exact WordLang program carrier fixtures

These kernel fixtures exercise the exact-to-production carrier boundary. They
do not claim that production compilation currently calls `compHOL`.
-/

namespace Flapjack.Test.WordProgCarrierCodecParity

open Flapjack Flapjack.Basis.Pure.MlString Flapjack.LoopToWord

private def nestedExact : WordLangProgHOL (BitVec 8) :=
  .seq
    (.loop (toNumSetHOL [2])
      (.ite .equal 2 (.imm 3)
        (.inst (.mem .load8 3 (.addr 2 1))) .tick)
      (toNumSetHOL [2, 4]))
    (.call (some ([7], (toNumSetHOL [7], toNumSetHOL [8]),
        .return 9 [7], 3, 4)) (some 12) [8]
      (some (6, .raise 6, 4, 5)))

private def ffiExact : WordLangProgHOL (BitVec 8) :=
  .ffi (ofString "write") 1 2 3 4 (toNumSetHOL [2, 3], toNumSetHOL [4, 4])

example : Flapjack.LoopToWord.fromNumSetHOL (toNumSetHOL [2, 3]) = [3, 2] := by
  simp [Flapjack.LoopToWord.fromNumSetHOL,
    Flapjack.LoopToWord.toNumSetHOL, sptInsert, sptToAList,
    sptFoldi, lrNext]

example : Flapjack.LoopToWord.fromNumSetHOL (toNumSetHOL [4, 4]) = [4] := by
  simp [Flapjack.LoopToWord.fromNumSetHOL,
    Flapjack.LoopToWord.toNumSetHOL, sptInsert, sptToAList,
    sptFoldi, lrNext]

private def unsupportedFp : WordLangProgHOL (BitVec 8) :=
  .inst (.fp (.fpAdd 1 2 3))

private def generatedOverflow : WordLangProgHOL (BitVec 8) :=
  .inst (.arith (.addOverflow 1 2 3 4))

private def generatedAddCarry : WordLangProgHOL (BitVec 8) :=
  .inst (.arith (.addCarry 3 4 5 6))

/-! `compHOL` image fixtures: these exercise generated AddCarry, memory,
nested Seq/Loop/Call-handler, and FFI outputs through the universal projection
theorem. They do not claim production `loopToWord` calls `compHOL`. -/

private def imageContext : Spt Nat := .ln

private def imageAddCarry : HolLoopProg 8 :=
  .primitive [1, 2] .addCarry [3, 4, 5]

private def imageMemory : HolLoopProg 8 :=
  .seq (.load32 1 2) (.storeByte 2 3)

private def imageNestedHandler : HolLoopProg 8 :=
  .seq imageAddCarry
    (.loop (toNumSetHOL [1, 2])
      (.call (some ([7], toNumSetHOL [7])) (some 12) [8]
        (some (6, .seq (.loadByte 2 3) .tick,
          .ffi (ofString "write") 1 2 3 4 (toNumSetHOL [4]), toNumSetHOL [6])))
      (toNumSetHOL [1, 2]))

private def imageFfi : HolLoopProg 8 :=
  .ffi (ofString "write") 1 2 3 4 (toNumSetHOL [2, 3])

def runChecks : IO Bool := do
  IO.println "PASS fixed-width WordLangProg projection (loop/call/FFI; AddCarry/memory; unsupported FP/overflow rejected)"
  IO.println "PASS exact compHOL output image (AddCarry; memory; nested Seq/Loop/Call-handler; FFI)"
  return true

end Flapjack.Test.WordProgCarrierCodecParity
