import Flapjack.Compiler.Backend.WordToStack.ProductionBitmapWrite
import Flapjack.Compiler.Backend.WordToStack.ProductionBitmapState

/-! Complete actual caller bitmap-write transport. This is Flapjack production
carrier infrastructure with no HOL declaration. The shared native codec and
consumer are used directly, and the allocator producer supplies the coloured GC
domain. This does not establish whole-body or final compiler simulation. -/
namespace Flapjack.ProductionBitmapWritePair
open RiscV RiscV.CakeRegAlloc Compiler.Backend.WordToStack
open Compiler.Backend.StackLang

/-- The native writer's whole program component depends only on its frame
branch and stored count. Both actual shared input boundaries match it, with no
bitmap equality or count-range hypothesis. -/
theorem programPair {width : Nat} [NeZero width] (label : Nat)
    (allocation : WordSpillState) (k slots : Nat) (state : WordStackBitmapState)
    (live : List Nat) (builder : List Nat → List Nat) (cutsets : Spt Unit × Spt Unit) :
    let actual := wordStackBitmapWriteWithBuilder (sourceWordStackConfig label allocation slots)
      k slots state live builder
    let native := Native.wLiveNative cutsets (ProductionBitmapTransport.encode state)
      (k, if slots = 0 then 0 else slots + 1, slots)
    natToHolProg (width := width) actual.1 = some native.1 ∧
      Compiler.Backend.StackToLab.Production.toNative? actual.1 = some native.1 := by
  dsimp only
  rw [ProductionBitmapWrite.writerCodec, ProductionBitmapWrite.writerConsumer]
  by_cases empty : slots = 0 <;>
    simp [Native.wLiveNative, insertBitmap, ProductionBitmapTransport.encode,
      empty, wordStackOffset, sourceWordStackConfig]

/-- Arbitrary native AppList prefixes commute with the whole writer observation.
The stored count stays independent of the prefix/data lengths. This supplies the
actual caller's empty-local-chunk/global-count convention without a new bound. -/
theorem nativePrefix {width : Nat} [NeZero width] (cutsets : Spt Unit × Spt Unit)
    (bitmaps : AppList (BitVec width) × Nat) (kf : Nat × Nat × Nat)
    (priorData : AppList (BitVec width)) :
    let plain := Native.wLiveNative cutsets bitmaps kf
    let prefixed := Native.wLiveNative cutsets (.append priorData bitmaps.1, bitmaps.2) kf
    (prefixed.1, appListAppend prefixed.2.1, prefixed.2.2) =
      (plain.1, appListAppend priorData ++ appListAppend plain.2.1, plain.2.2) := by
  have flattenAppend (left right : AppList (BitVec width)) :
      appListAppend (.append left right) = appListAppend left ++ appListAppend right :=
    (appListAppend_thm left right []).1
  by_cases empty : kf.2.1 = 0 <;>
    simp [Native.wLiveNative, empty, insertBitmap, flattenAppend, List.append_assoc]

/-- Complete simultaneous program/data/count result at the actual FromWord
caller. Genuine source row, allocator run, original ISA and selected GC-name
occurrences are retained. No desired bitmap relation, target run or simulation
callback is assumed. -/
theorem sourceRowWritePair {width : Nat} [NeZero width]
    (functions : List (Nat × List Nat × LoopProg (BitVec width)))
    (label arity : Nat) (body : WordProg (BitVec width))
    (row : (label, arity, body) ∈ panToWordCompileProg functions)
    (config : Compiler.Encoders.Asm.AsmConfigExact width) (target : config.isa = .riscv)
    (output : WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState)
    (produced : cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy label
      (wordSsaAbiParameters arity) (wordBeforeSsaAllocatorBody body) = some output)
    (renamedProgram : WordProg (BitVec width)) (state : WordStackBitmapState)
    (nonGc : Spt Unit) (live : List Nat)
    (consumed : ∀ name ∈ live, ProductionGcCutsets.GcName name output.2.2.1) :
    ∃ retained : CakeAllocationWithColour (BitVec width),
      retained.toLegacy = output ∧
      let slots := cakeWordFrameSlots output.2.2.2 (wordSsaAbiParameters arity) renamedProgram
      let actualConfig := sourceWordStackConfig label output.2.2.2 slots
      let actual := wordStackBitmapWriteWithBuilder actualConfig cakeRiscVRegisterCount slots
        state live (wordStackLiveBitmapFromLocations actualConfig slots width)
      let native := Native.wLiveNative
        (nonGc, LoopToWord.toNumSetHOL (live.map (CakeAlloc.totalColour retained.colouring)))
        (ProductionBitmapTransport.encode state)
        (cakeRiscVRegisterCount, if slots = 0 then 0 else slots + 1, slots)
      (natToHolProg (width := width) actual.1,
        appListAppend (ProductionBitmapTransport.encode (width := width) actual.2).1,
        (ProductionBitmapTransport.encode (width := width) actual.2).2) =
      (some native.1, appListAppend native.2.1, native.2.2) ∧
      Compiler.Backend.StackToLab.Production.toNative? actual.1 = some native.1 := by
  obtain ⟨retained, retainedOutput, bitmapState⟩ := ProductionBitmapState.sourceRowStatePair
    functions label arity body row config target output produced renamedProgram state nonGc live consumed
  refine ⟨retained, retainedOutput, ?_⟩
  dsimp only
  obtain ⟨code, consumer⟩ := programPair (width := width) label output.2.2.2
    cakeRiscVRegisterCount
    (cakeWordFrameSlots output.2.2.2 (wordSsaAbiParameters arity) renamedProgram)
    state live
    (wordStackLiveBitmapFromLocations
      (sourceWordStackConfig label output.2.2.2
        (cakeWordFrameSlots output.2.2.2 (wordSsaAbiParameters arity) renamedProgram))
      (cakeWordFrameSlots output.2.2.2 (wordSsaAbiParameters arity) renamedProgram) width)
    (nonGc, LoopToWord.toNumSetHOL (live.map (CakeAlloc.totalColour retained.colouring)))
  exact ⟨Prod.ext code bitmapState, consumer⟩

/-- Full actual caller transport under an arbitrary preceding bitmap chunk.
In particular, local data=[] and the global stored count instantiate this
without assuming count equals accumulated bitmap length. -/
theorem sourceRowWritePairWithPrefix {width : Nat} [NeZero width]
    (functions : List (Nat × List Nat × LoopProg (BitVec width)))
    (label arity : Nat) (body : WordProg (BitVec width))
    (row : (label, arity, body) ∈ panToWordCompileProg functions)
    (config : Compiler.Encoders.Asm.AsmConfigExact width) (target : config.isa = .riscv)
    (output : WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState)
    (produced : cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy label
      (wordSsaAbiParameters arity) (wordBeforeSsaAllocatorBody body) = some output)
    (renamedProgram : WordProg (BitVec width)) (state : WordStackBitmapState)
    (priorData : AppList (BitVec width)) (nonGc : Spt Unit) (live : List Nat)
    (consumed : ∀ name ∈ live, ProductionGcCutsets.GcName name output.2.2.1) :
    ∃ retained : CakeAllocationWithColour (BitVec width),
      retained.toLegacy = output ∧
      let slots := cakeWordFrameSlots output.2.2.2 (wordSsaAbiParameters arity) renamedProgram
      let actualConfig := sourceWordStackConfig label output.2.2.2 slots
      let actual := wordStackBitmapWriteWithBuilder actualConfig cakeRiscVRegisterCount slots
        state live (wordStackLiveBitmapFromLocations actualConfig slots width)
      let native := Native.wLiveNative
        (nonGc, LoopToWord.toNumSetHOL (live.map (CakeAlloc.totalColour retained.colouring)))
        (.append priorData (ProductionBitmapTransport.encode state).1, state.length)
        (cakeRiscVRegisterCount, if slots = 0 then 0 else slots + 1, slots)
      (natToHolProg (width := width) actual.1,
        appListAppend priorData ++
          appListAppend (ProductionBitmapTransport.encode (width := width) actual.2).1,
        (ProductionBitmapTransport.encode (width := width) actual.2).2) =
      (some native.1, appListAppend native.2.1, native.2.2) ∧
      Compiler.Backend.StackToLab.Production.toNative? actual.1 = some native.1 := by
  obtain ⟨retained, retainedOutput, codeState, consumer⟩ := sourceRowWritePair
    functions label arity body row config target output produced renamedProgram state nonGc live consumed
  refine ⟨retained, retainedOutput, ?_⟩
  dsimp only
  have prefixResult := nativePrefix (width := width)
    (nonGc, LoopToWord.toNumSetHOL (live.map (CakeAlloc.totalColour retained.colouring)))
    (ProductionBitmapTransport.encode state)
    (cakeRiscVRegisterCount,
      if cakeWordFrameSlots output.2.2.2 (wordSsaAbiParameters arity) renamedProgram = 0
      then 0 else cakeWordFrameSlots output.2.2.2 (wordSsaAbiParameters arity) renamedProgram + 1,
      cakeWordFrameSlots output.2.2.2 (wordSsaAbiParameters arity) renamedProgram) priorData
  have prefixedCore := congrArg
    (fun observation : Option (HolProg width) × List (BitVec width) × Nat =>
      (observation.1, appListAppend priorData ++ observation.2.1, observation.2.2)) codeState
  have prefixedNative := congrArg
    (fun observation : HolProg width × List (BitVec width) × Nat =>
      (some observation.1, observation.2.1, observation.2.2)) prefixResult
  have prefixedProgram := congrArg
    (fun observation : HolProg width × List (BitVec width) × Nat => some observation.1) prefixResult
  exact ⟨prefixedCore.trans prefixedNative.symm, consumer.trans prefixedProgram.symm⟩

end Flapjack.ProductionBitmapWritePair
