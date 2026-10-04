import Flapjack.Compiler.Backend.WordToStack.ProductionStoreConsts
import Flapjack.Compiler.Backend.StackLang.ProductionMacros

namespace Flapjack.Test.WordToStackStoreConstsCaller
open Flapjack RiscV Compiler.Backend.StackLang

private def config : WordStackConfig :=
  { locations := [], scratch := 22, stackBase := 23, specialScratch := 11 }

private def constants8 : List (Bool × BitVec 8) := [(true, 255), (false, 1)]

/-- Actual fused consumer keeps source register1/stub6 despite scratch11 and
the legacy caller's stub1; count is arbitrary, including beyond word range. -/
example (index : Nat) :
    wordToStackProgWordWithLocationBitmapsFused config 22 31 0 8 (some 1)
      { data := [4], length := index } (.storeConsts 9 10 11 12 constants8) =
    some (.seq (.inst (.const 1 index)) (.storeConsts 22 23 (some 6)),
      { data := [4, 5, 255, 1], length := index + 3 }) := by
  rw [ProductionStoreConsts.actualCaller]
  simp [wordStackStoreConstsNativeWithBitmaps, wordStackInsertBitmap, constants8,
    Compiler.Backend.WordToStack.constWordsToBitmapW,
    Compiler.Backend.WordToStack.chunkToBitmapW, Compiler.Backend.WordToStack.chunkToBitsW]
  rfl

/-- Original HOL below8 row. -/
example : WordPayloads.natToWords 8
    (wordStackStoreConstsNativeWithBitmaps 22 { data := [4], length := 255 } constants8).1 =
    .seq (.inst (.const 1 255)) (.storeConsts 22 23 (some 6)) := rfl

/-- Original HOL wrap8 row, through the actual word-payload projection. -/
example : WordPayloads.natToWords 8
    (wordStackStoreConstsNativeWithBitmaps 22 { data := [4], length := 256 } constants8).1 =
    .seq (.inst (.const 1 0)) (.storeConsts 22 23 (some 6)) := rfl

/-- Original HOL wrap64 row. -/
example : WordPayloads.natToWords 64
    (wordStackStoreConstsNativeWithBitmaps 22 { data := [4], length := 18446744073709551616 }
      ([(true, 255), (false, 1)] : List (Bool × BitVec 64))).1 =
    .seq (.inst (.const 1 0)) (.storeConsts 22 23 (some 6)) := rfl

/-- Strict chunk boundary retains the original final empty header. -/
example : (wordStackStoreConstsNativeWithBitmaps 22 { data := [4], length := 0 }
    (List.replicate 7 (true, (255 : BitVec 8)))).2 =
    { data := [4,255,255,255,255,255,255,255,255,1], length := 9 } := by
  simp [wordStackStoreConstsNativeWithBitmaps, wordStackInsertBitmap,
    Compiler.Backend.WordToStack.constWordsToBitmapW,
    Compiler.Backend.WordToStack.chunkToBitmapW, Compiler.Backend.WordToStack.chunkToBitsW]

/-- Width1 escape and word wrapping, with the original unrestricted count. -/
example : (wordStackStoreConstsNativeWithBitmaps 22 { data := [4], length := 2 }
    ([(true, 1), (false, 0)] : List (Bool × BitVec 1))).2 =
    { data := [4,1,1,0], length := 5 } := by
  simp [wordStackStoreConstsNativeWithBitmaps, wordStackInsertBitmap,
    Compiler.Backend.WordToStack.constWordsToBitmapW,
    Compiler.Backend.WordToStack.chunkToBitmapW, Compiler.Backend.WordToStack.chunkToBitsW]

/-- A wrapped source instruction is accepted by the real macro projection;
it does not inherit the rejected Nat macro's out-of-width guard. -/
example : ProductionMacros.projectMacros (WordPayloads.natToWords 8
    (wordStackStoreConstsNativeWithBitmaps 22 { data := [4], length := 256 } constants8).1) =
    some (.seq (.inst (.const 1 0)) (.storeConsts 22 23 (some 6))) := by
  simp [ProductionMacros.projectMacros, WordPayloads.natToWords, WordPayloads.mapProg,
    WordPayloads.mapInst, wordStackStoreConstsNativeWithBitmaps, wordStackInsertBitmap,
    storeConstsStubLocation, wordNumStubs]
  rfl

end Flapjack.Test.WordToStackStoreConstsCaller
