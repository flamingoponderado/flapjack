import Flapjack.Compiler.Backend.WordToStack.ProductionBitmapConsumption

/-! Structural congruence for the executed fused bitmap traversal. These are
Flapjack compiler facts, not HOL semantic theorem ports. -/
namespace Flapjack.ProductionBitmapTraversal
open RiscV RiscV.CakeRegAlloc ProductionGcCutsets

/-- The fused compiler observes a bitmap builder only on actual GC cutsets.
This congruence is infrastructure; concrete caller equality must discharge the
builder condition from the allocator and cleanup facts. -/
theorem fusedBuilderCongruence {width : Nat} [NeZero width]
    (config : WordStackConfig) (first second : List Nat → List Nat)
    (registerCount bitmapRegister frameSlots wordBits : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState)
    (program : WordProg (Word width))
    (agree : ∀ live, (∀ name ∈ live, GcName name program) → first live = second live) :
    wordToStackProgWordWithBitmapBuilder config first registerCount bitmapRegister
      frameSlots wordBits storeConstsStub state program =
    wordToStackProgWordWithBitmapBuilder config second registerCount bitmapRegister
      frameSlots wordBits storeConstsStub state program := by
  induction measure : sizeOf program using Nat.strong_induction_on generalizing program state with
  | h measure ih =>
    have recurse (sub : WordProg (Word width))
        (smaller : sizeOf sub < sizeOf program)
        (inside : ∀ name, GcName name sub → GcName name program)
        (subState : WordStackBitmapState) :
        wordToStackProgWordWithBitmapBuilder config first registerCount bitmapRegister
          frameSlots wordBits storeConstsStub subState sub =
        wordToStackProgWordWithBitmapBuilder config second registerCount bitmapRegister
          frameSlots wordBits storeConstsStub subState sub := by
      apply ih (sizeOf sub) (by omega) subState sub
      · intro live selected
        exact agree live (fun name member => inside name (selected name member))
      · rfl
    cases program <;> try simp only [wordToStackProgWordWithBitmapBuilder]

    case seq left right =>
      have leftEq := recurse left (by simp; omega)
        (fun name inside => GcName.seqLeft left right inside)
      have rightEq := recurse right (by simp)
        (fun name inside => GcName.seqRight left right inside)
      conv_lhs => rw [wordToStackProgWordWithBitmapBuilder.eq_def]
      conv_rhs => rw [wordToStackProgWordWithBitmapBuilder.eq_def]
      dsimp only
      simp_rw [leftEq, rightEq]
      congr 1
      split <;> try rfl
      rename_i originalFirst originalSecond destination source name operator condition value rest
      have restEq := recurse rest (by simp; omega)
        (fun name inside => GcName.seqRight _ _ (GcName.seqRight _ _ inside))
      simp_rw [restEq]
    case inst instruction =>
      cases instruction <;> try simp only [wordToStackProgWordWithBitmapBuilder]
      case arith instruction =>
        cases instruction <;> simp only [wordToStackProgWordWithBitmapBuilder]
    case store address value =>
      cases address <;> simp only [wordToStackProgWordWithBitmapBuilder]
    case loop before body after =>
      have bodyEq := recurse body (by simp; omega) (fun name inside => GcName.loop before after body inside)
      simp_rw [bodyEq]
    case mustTerminate body =>
      exact recurse body (by simp) (fun name inside => GcName.mustTerminate body inside) state
    case ite op condition right left rightBody =>
      have leftEq := recurse left (by simp; omega)
        (fun name inside => GcName.iteLeft op condition right left rightBody inside)
      have rightEq := recurse rightBody (by simp)
        (fun name inside => GcName.iteRight op condition right left rightBody inside)
      simp_rw [leftEq, rightEq]
    case call returns target arguments handler =>
      rcases returns with _ | ⟨values, ⟨other, live⟩, body, l1, l2⟩
      · rcases target with _ | target <;>
          simp only [wordToStackProgWordWithBitmapBuilder]
      · have bitmapEq := agree live
          (fun name member => GcName.call values other live body l1 l2 target arguments handler member)
        have bodyEq := recurse body (by simp; omega)
          (fun name inside => GcName.returnBody values other live body l1 l2 target arguments handler inside)
        rcases handler with _ | ⟨exception, hbody, h1, h2⟩
        · rcases target with _ | target
          all_goals simp only [wordToStackProgWordWithBitmapBuilder,
            wordStackCallLiveBitmapWord, wordStackBitmapWriteWithBuilder]
          all_goals simp_rw [bitmapEq, bodyEq]
        · have handlerEq := recurse hbody (by simp; omega)
            (fun name inside => GcName.handlerBody values other live body l1 l2 target arguments
              exception hbody h1 h2 inside)
          rcases target with _ | target
          all_goals simp only [wordToStackProgWordWithBitmapBuilder,
            wordStackCallLiveBitmapWord, wordStackBitmapWriteWithBuilder]
          all_goals simp_rw [bitmapEq, bodyEq, handlerEq]
    case alloc destination cutsets =>
      rcases cutsets with ⟨other, live⟩
      have bitmapEq := agree live (fun name member => GcName.alloc destination other live member)
      simp only [wordToStackProgWordWithBitmapBuilder, wordStackAllocWithBitmapBuilder,
        wordStackBitmapWriteWithBuilder]
      rw [bitmapEq]

/-- Complete actual fused traversal uses the original colour bitmap on every
selected post-remove GC cutset. Equality covers the entire Option result,
including failures, code and complete threaded bitmap state. The bitmap-builder
condition is discharged here from the real allocation and cleanup branches. -/
theorem retainedAfterRemove_fusedBitmap {width : Nat} [NeZero width]
    (copy dead : WordProg (BitVec width) → WordProg (BitVec width))
    (unreach : WordProg (BitVec width) → Option (WordProg (BitVec width)))
    (ssa : Nat → WordProg (BitVec width) → Option (WordSsaState × List Nat × WordProg (BitVec width)))
    (label : Nat) (parameters : List Nat) (source : WordProg (BitVec width))
    (output : CakeRegAlloc.CakeAllocationWithColour (BitVec width))
    (produced : CakeRegAlloc.cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy
      copy dead unreach ssa label parameters source = some output)
    (input : ProductionCleanupConventions.NativeInput output.program)
    (result : WordProg (BitVec width))
    (removed : wordRemoveMustTerminateViaHOL? output.program = some result)
    (config : Compiler.Encoders.Asm.AsmConfigExact width) (target : config.isa = .riscv)
    (bitmapRegister : Nat) (storeConstsStub : Option Nat) (state : WordStackBitmapState) :
    let slots := (CakeRegAlloc.cakeColourFrameSlots cakeRiscVRegisterCount parameters
      output.program output.colouring).1
    let locationConfig := sourceWordStackConfig label output.allocation slots
    wordToStackProgWordWithLocationBitmapsFused locationConfig cakeRiscVRegisterCount
      bitmapRegister slots width storeConstsStub state result =
    wordToStackProgWordWithBitmapBuilder locationConfig
      (fun live => CakeAlloc.writeBitmap (live.map (CakeAlloc.totalColour output.colouring))
        cakeRiscVRegisterCount slots width)
      cakeRiscVRegisterCount bitmapRegister slots width storeConstsStub state result := by
  dsimp only
  apply fusedBuilderCongruence
  intro live consumed
  exact ProductionBitmapConsumption.retainedAfterRemove_liveBitmap
    copy dead unreach ssa label parameters source output produced input result removed
    config target live consumed

/-- The actual source-row allocator and cleanup caller supply the whole fused
bitmap traversal equality. No live-list selection, desired input convention,
builder equality or successful target compilation premise remains. Allocation
and cleanup success are the caller's observed branches; their errors are outside
this bitmap-local statement. -/
theorem sourceRowAfterRemove_fusedBitmap {width : Nat} [NeZero width]
    (functions : List (Nat × List Nat × LoopProg (BitVec width)))
    (label arity : Nat) (body : WordProg (BitVec width))
    (row : (label, arity, body) ∈ panToWordCompileProg functions)
    (config : Compiler.Encoders.Asm.AsmConfigExact width) (target : config.isa = .riscv)
    (output : WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState)
    (produced : cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy label
      (wordSsaAbiParameters arity) (wordBeforeSsaAllocatorBody body) = some output)
    (result : WordProg (BitVec width))
    (removed : wordRemoveMustTerminateViaHOL? output.2.2.1 = some result)
    (bitmapRegister : Nat) (storeConstsStub : Option Nat) (state : WordStackBitmapState) :
    ∃ retained : CakeAllocationWithColour (BitVec width),
      retained.toLegacy = output ∧
      let slots := cakeWordFrameSlots output.2.2.2 (wordSsaAbiParameters arity) result
      let locationConfig := sourceWordStackConfig label output.2.2.2 slots
      wordToStackProgWordWithLocationBitmapsFused locationConfig cakeRiscVRegisterCount
        bitmapRegister slots width storeConstsStub state result =
      wordToStackProgWordWithBitmapBuilder locationConfig
        (fun live => CakeAlloc.writeBitmap (live.map (CakeAlloc.totalColour retained.colouring))
          cakeRiscVRegisterCount slots width)
        cakeRiscVRegisterCount bitmapRegister slots width storeConstsStub state result := by
  have input := ProductionCleanupConventions.panToWordRow_input
    functions label arity body row config output produced
  obtain ⟨native, encoded⟩ := Option.isSome_iff_exists.mp
    (wordLangProgToHOL_wordBeforeSsaAllocatorBody_isSome body
      (ProductionCleanupConventions.panToWordRow_codec functions label arity body row))
  unfold cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy at produced
  simp only [encoded] at produced
  obtain ⟨retained, actualRun, same⟩ := Option.map_eq_some_iff.mp produced
  subst output
  refine ⟨retained, rfl, ?_⟩
  change let slots := cakeWordFrameSlots retained.allocation (wordSsaAbiParameters arity) result
         let locationConfig := sourceWordStackConfig label retained.allocation slots
         wordToStackProgWordWithLocationBitmapsFused locationConfig cakeRiscVRegisterCount
           bitmapRegister slots width storeConstsStub state result =
         wordToStackProgWordWithBitmapBuilder locationConfig
           (fun live => CakeAlloc.writeBitmap (live.map (CakeAlloc.totalColour retained.colouring))
             cakeRiscVRegisterCount slots width)
           cakeRiscVRegisterCount bitmapRegister slots width storeConstsStub state result
  rw [ProductionBitmapCaller.retainedConsumer_frameSlots _ _ _ _ label _ _ retained actualRun result]
  exact retainedAfterRemove_fusedBitmap _ _ _ _ label _ _ retained actualRun
    input result removed config target bitmapRegister storeConstsStub state

/-- Every actual post-remove GC site has the whole original writer's
program/data/count pair, with arbitrary incoming data and stored count. The
complete traversal above establishes that only such sites consume the builder. -/
theorem retainedAfterRemove_writePair {width : Nat} [NeZero width]
    (copy dead : WordProg (BitVec width) → WordProg (BitVec width))
    (unreach : WordProg (BitVec width) → Option (WordProg (BitVec width)))
    (ssa : Nat → WordProg (BitVec width) → Option (WordSsaState × List Nat × WordProg (BitVec width)))
    (label : Nat) (parameters : List Nat) (source : WordProg (BitVec width))
    (output : CakeAllocationWithColour (BitVec width))
    (produced : cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy
      copy dead unreach ssa label parameters source = some output)
    (input : ProductionCleanupConventions.NativeInput output.program)
    (result : WordProg (BitVec width))
    (removed : wordRemoveMustTerminateViaHOL? output.program = some result)
    (config : Compiler.Encoders.Asm.AsmConfigExact width) (target : config.isa = .riscv)
    (state : WordStackBitmapState) (nonGc : Spt Unit) (live : List Nat)
    (selected : ∀ name ∈ live, GcName name result) :
    let slots := (cakeColourFrameSlots cakeRiscVRegisterCount parameters
      output.program output.colouring).1
    let locationConfig := sourceWordStackConfig label output.allocation slots
    let actual := wordStackBitmapWriteWithBuilder locationConfig cakeRiscVRegisterCount slots
      state live (wordStackLiveBitmapFromLocations locationConfig slots width)
    let native := Compiler.Backend.WordToStack.Native.wLiveNative
      (nonGc, LoopToWord.toNumSetHOL (live.map (CakeAlloc.totalColour output.colouring)))
      (ProductionBitmapTransport.encode state)
      (cakeRiscVRegisterCount, if slots = 0 then 0 else slots + 1, slots)
    (Compiler.Backend.StackLang.natToHolProg (width := width) actual.1,
      appListAppend (ProductionBitmapTransport.encode (width := width) actual.2).1,
      (ProductionBitmapTransport.encode (width := width) actual.2).2) =
      (some native.1, appListAppend native.2.1, native.2.2) ∧
      Compiler.Backend.StackToLab.Production.toNative? actual.1 = some native.1 := by
  have bitmap := ProductionBitmapConsumption.retainedAfterRemove_liveBitmap
    copy dead unreach ssa label parameters source output produced input result removed
    config target live selected
  dsimp only at bitmap ⊢
  obtain ⟨code, consumer⟩ := ProductionBitmapWritePair.programPair (width := width)
    label output.allocation cakeRiscVRegisterCount
    (cakeColourFrameSlots cakeRiscVRegisterCount parameters output.program output.colouring).1
    state live
    (wordStackLiveBitmapFromLocations
      (sourceWordStackConfig label output.allocation
        (cakeColourFrameSlots cakeRiscVRegisterCount parameters output.program output.colouring).1)
      (cakeColourFrameSlots cakeRiscVRegisterCount parameters output.program output.colouring).1 width)
    (nonGc, LoopToWord.toNumSetHOL (live.map (CakeAlloc.totalColour output.colouring)))
  refine ⟨Prod.ext code ?_, consumer⟩
  by_cases empty : (cakeColourFrameSlots cakeRiscVRegisterCount parameters
      output.program output.colouring).1 = 0 <;>
    simp [wordStackBitmapWriteWithBuilder, Compiler.Backend.WordToStack.Native.wLiveNative,
      empty, wordStackInsertBitmap, Compiler.Backend.WordToStack.insertBitmap,
      ProductionBitmapState.packed, ProductionBitmapTransport.encode,
      appListAppend, appendAux, List.map_append, bitmap]

end Flapjack.ProductionBitmapTraversal
