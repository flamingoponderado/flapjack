import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.CompHOLImage

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

private def nestedExecutable : WordProg (BitVec 8) :=
  .seq
    (.loop (Flapjack.LoopToWord.fromNumSetHOL
        (toNumSetHOL [2]))
      (.ite .equal 2 (.imm 3)
        (.inst (.memOffset .load8 3 2 1)) .tick)
      (Flapjack.LoopToWord.fromNumSetHOL (toNumSetHOL [2, 4])))
    (.call (some ([7],
        (Flapjack.LoopToWord.fromNumSetHOL (toNumSetHOL [7]),
          Flapjack.LoopToWord.fromNumSetHOL (toNumSetHOL [8])),
        .return 9 [7], 3, 4)) (some 12) [8]
      (some (6, .raise 6, 4, 5)))

example : wordLangProgFromHOL nestedExact = some nestedExecutable := by
  simp [nestedExact, nestedExecutable, wordLangProgFromHOL,
    wordLangInstFromHOL, wordCutsetsFromHOL, toNumSetHOL, fromNumSetHOL,
    sptInsert, sptToAList, sptFoldi, lrNext]

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

example : wordLangProgFromHOL ffiExact =
    some (.ffi "write" 1 2 3 4
      ([3, 2], [4])) := by
  simp [ffiExact, wordLangProgFromHOL,
    wordCutsetsFromHOL, toNumSetHOL, fromNumSetHOL,
    toStringOfBytes, ofString, sptInsert, sptToAList, sptFoldi, lrNext]

private def unsupportedFp : WordLangProgHOL (BitVec 8) :=
  .inst (.fp (.fpAdd 1 2 3))

example : wordLangProgFromHOL unsupportedFp = none := by
  simp [unsupportedFp, wordLangProgFromHOL, wordLangInstFromHOL]

private def unsupportedOverflow : WordLangProgHOL (BitVec 8) :=
  .inst (.arith (.addOverflow 1 2 3 4))

example : wordLangProgFromHOL unsupportedOverflow = none := by
  simp [unsupportedOverflow, wordLangProgFromHOL,
    wordLangInstFromHOL, wordLangArithFromHOL]

private def generatedAddCarry : WordLangProgHOL (BitVec 8) :=
  .inst (.arith (.addCarry 3 4 5 6))

example : wordLangProgFromHOL generatedAddCarry =
    some (.inst (.arith (.cakeAddCarry 3 5 6 4))) := by
  simp [generatedAddCarry, wordLangProgFromHOL,
    wordLangInstFromHOL, wordLangArithFromHOL]

example : wordLangInstFromHOL
    (.const 3 (BitVec.ofNat 8 9) : WordLangInst (BitVec 8)) =
      some (.const 3 (BitVec.ofNat 8 9)) := by
  rfl

example : wordLangInstFromHOL
    (.mem .load32 3 (.addr 2 0) : WordLangInst (BitVec 8)) =
      some (.mem .load32 3 2) := by
  simp [wordLangInstFromHOL]

example : wordLangInstFromHOL (WordLangInst.skip : WordLangInst (BitVec 8)) = none := by
  rfl

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

example : wordLangProgFromHOL
    (LoopToWord.compHOL imageContext imageAddCarry (7, 11)).1 ≠ none :=
  wordLangProgFromHOL_compHOL_ne_none imageContext imageAddCarry (7, 11)

example : wordLangProgFromHOL
    (LoopToWord.compHOL imageContext imageMemory (7, 11)).1 ≠ none :=
  wordLangProgFromHOL_compHOL_ne_none imageContext imageMemory (7, 11)

example : wordLangProgFromHOL
    (LoopToWord.compHOL imageContext imageNestedHandler (7, 11)).1 ≠ none :=
  wordLangProgFromHOL_compHOL_ne_none imageContext imageNestedHandler (7, 11)

example : wordLangProgFromHOL
    (LoopToWord.compHOL imageContext imageFfi (7, 11)).1 ≠ none :=
  wordLangProgFromHOL_compHOL_ne_none imageContext imageFfi (7, 11)

def runChecks : IO Bool := do
  IO.println "PASS fixed-width WordLangProg projection (loop/call/FFI; AddCarry/memory; unsupported FP/overflow rejected)"
  IO.println "PASS exact compHOL output image (AddCarry; memory; nested Seq/Loop/Call-handler; FFI)"
  return true

end Flapjack.Test.WordProgCarrierCodecParity
