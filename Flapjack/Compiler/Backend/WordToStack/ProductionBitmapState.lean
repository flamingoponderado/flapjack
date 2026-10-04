import Flapjack.Compiler.Backend.WordToStack.ProductionBitmapCaller
import Flapjack.Compiler.Backend.WordToStack.NativeLive

/-! Flapjack production bitmap-state carrier correspondence. These statements
have no HOL original: they relate actual Nat/list output to the existing native
Spt/word/AppList compiler. They retain arbitrary stored counts and duplicate GC
names, and do not assume the bitmap/state equality being established. -/
namespace Flapjack.ProductionBitmapState
open RiscV RiscV.CakeRegAlloc Compiler.Backend.WordToStack

/-- Exact packing from a production coloured GC-name list through the canonical
Spt constructor. Enumeration order and duplicate names do not affect packing. -/
theorem packed {width : Nat} [NeZero width] (live : List Nat) (k slots : Nat) :
    writeBitmapExact (width := width) (LoopToWord.toNumSetHOL live) k slots =
      (CakeAlloc.writeBitmap live k slots width).map (BitVec.ofNat width) := by
  rw [writeBitmapExact_eq_domain]
  have sameDomain : ∀ name,
      name ∈ (sptToAList (LoopToWord.toNumSetHOL live)).map Prod.fst ↔ name ∈ live := by
    intro name
    rw [sptMemMapFstToAList, LoopToWord.sptDomain_toNumSetHOL]
  rw [writeBitmapHOL_domain_insensitive _ live k slots sameDomain]
  exact (CakeAlloc.writeBitmap_eq_writeBitmapHOL live k slots).symm

/-- Complete native bitmap-state/count projection of the actual insertion
branch, including zero frames and inconsistent count/data-length inputs. -/
theorem statePair {width : Nat} [NeZero width]
    (config : WordStackConfig) (k slots : Nat) (state : WordStackBitmapState)
    (nonGc live : List Nat) :
    let actual := wordStackBitmapWriteWithBuilder config k slots state live
      (fun names => CakeAlloc.writeBitmap names k slots width)
    let native := Native.wLiveNative
      (LoopToWord.toNumSetHOL nonGc, LoopToWord.toNumSetHOL live)
      (ProductionBitmapTransport.encode state)
      (k, if slots = 0 then 0 else slots + 1, slots)
    (appListAppend (ProductionBitmapTransport.encode (width := width) actual.2).1,
      (ProductionBitmapTransport.encode (width := width) actual.2).2) =
    (appListAppend native.2.1, native.2.2) := by
  by_cases empty : slots = 0 <;>
    simp [wordStackBitmapWriteWithBuilder, Native.wLiveNative, empty,
      wordStackInsertBitmap, insertBitmap, packed, ProductionBitmapTransport.encode,
      appListAppend, appendAux, List.map_append]

/-- Actual FromWord producer supplies the live-domain/colouring correspondence
internally. The whole returned bitmap state/count matches the native writer;
no bitmap equality, post-state relation, or successful lowering is assumed. -/
theorem sourceRowStatePair {width : Nat} [NeZero width]
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
      (appListAppend (ProductionBitmapTransport.encode (width := width) actual.2).1,
        (ProductionBitmapTransport.encode (width := width) actual.2).2) =
      (appListAppend native.2.1, native.2.2) := by
  obtain ⟨retained, retainedOutput, bitmap⟩ := ProductionBitmapCaller.panToWordRow_liveBitmap
    functions label arity body row config target output produced renamedProgram live consumed
  refine ⟨retained, retainedOutput, ?_⟩
  dsimp only
  by_cases empty : cakeWordFrameSlots output.2.2.2
      (wordSsaAbiParameters arity) renamedProgram = 0 <;>
    simp [wordStackBitmapWriteWithBuilder, Native.wLiveNative, empty,
      wordStackInsertBitmap, insertBitmap, packed, ProductionBitmapTransport.encode,
      appListAppend, appendAux, List.map_append, bitmap]

end Flapjack.ProductionBitmapState
