import Flapjack.Compiler.Backend.WordToStack.ProductionBitmapTransport
import Flapjack.Compiler.Backend.StackLang.ProductionCodec
import Flapjack.Compiler.Backend.StackLang.WordPayloads
import Flapjack.Compiler.Backend.StackLang.ProductionMacros

namespace Flapjack.ProductionStoreConsts
open RiscV Compiler.Backend.WordToStack Compiler.Backend.StackLang

/-- The actual word-facing constructor consumes the reviewed source producer.
All configurations, stored counts, constants and irrelevant source registers
are retained; no scratch-register or index-bound premise is required. This
production caller factoring has no separate HOL declaration. -/
theorem actualCaller {width : Nat} [NeZero width]
    (config : WordStackConfig) (k bitmapRegister frameSlots wordBits : Nat)
    (stub : Option Nat) (state : WordStackBitmapState)
    (a b c d : Nat) (constants : List (Bool × BitVec width)) :
    wordToStackProgWordWithLocationBitmapsFused config k bitmapRegister frameSlots
      wordBits stub state (.storeConsts a b c d constants) =
      some (wordStackStoreConstsNativeWithBitmaps k state constants) := by
  simp only [wordToStackProgWordWithLocationBitmapsFused, wordToStackProgWordWithBitmapBuilder]

/-- Full original StoreConsts code at the executed word-payload boundary,
including arbitrary index wrapping and the original fixed stub location.
This is a production codec equality, not a replacement semantic theorem port. -/
theorem code {width : Nat} [NeZero width]
    (config : Compiler.Encoders.Asm.AsmConfigExact width) (perf : Bool)
    (state : WordStackBitmapState) (k frames extra a b c d : Nat)
    (constants : List (Bool × BitVec width)) :
    holProgToProduction
      (Native.compNative config perf (.storeConsts a b c d constants)
        (ProductionBitmapTransport.encode state) (k, frames, extra)).1 =
      some (WordPayloads.natToWords width
        (wordStackStoreConstsNativeWithBitmaps k state constants).1) := by
  simp [Native.compNative, wordStackStoreConstsNativeWithBitmaps, wordStackInsertBitmap,
    insertBitmap, ProductionBitmapTransport.encode, holProgToProduction,
    Compiler.Backend.holProgToProgW, progToProduction, WordPayloads.natToWords,
    WordPayloads.mapProg, WordPayloads.mapInst, Prog.map,
    Compiler.Encoders.Asm.HolInst.toWordLangInst, wordLangInstFromHOL]

/-- Complete projected native bitmap state, not merely the inserted bitmap or
index. Every stored word, the arbitrary original count, and the increment are
retained. AppList tree shape is observed through its original flattening.
This production representation equality has no separate HOL declaration. -/
theorem state {width : Nat} [NeZero width]
    (config : Compiler.Encoders.Asm.AsmConfigExact width) (perf : Bool)
    (input : WordStackBitmapState) (k frames extra a b c d : Nat)
    (constants : List (Bool × BitVec width)) :
    let actual := wordStackStoreConstsNativeWithBitmaps k input constants
    let native := Native.compNative config perf (.storeConsts a b c d constants)
      (ProductionBitmapTransport.encode input) (k, frames, extra)
    (appListAppend (ProductionBitmapTransport.encode (width := width) actual.2).1,
      actual.2.length) = (appListAppend native.2.1, native.2.2) := by
  simp [Native.compNative, wordStackStoreConstsNativeWithBitmaps, wordStackInsertBitmap,
    insertBitmap, ProductionBitmapTransport.encode, appListAppend, appendAux,
    List.map_append, List.map_map, Function.comp_def]

/-- Every source index survives the actual macro boundary. In particular no
out-of-width index bound is needed: the instruction payload has already been
wrapped by the reviewed word boundary. No separate HOL declaration exists. -/
theorem macroBoundary {width : Nat} [NeZero width]
    (input : WordStackBitmapState) (k : Nat) (constants : List (Bool × BitVec width)) :
    let actual := WordPayloads.natToWords width
      (wordStackStoreConstsNativeWithBitmaps k input constants).1
    ProductionMacros.projectMacros actual = some actual := by
  apply ProductionMacros.projectMacros_of_noMacros
  simp [wordStackStoreConstsNativeWithBitmaps, wordStackInsertBitmap,
    WordPayloads.natToWords, WordPayloads.mapProg, WordPayloads.mapInst,
    ProductionMacros.noMacros]

end Flapjack.ProductionStoreConsts
