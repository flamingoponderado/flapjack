import Flapjack.Compiler.Backend.StackToLab.ExecutedInput

namespace Flapjack.Test.StackToLabExecutedInput
open Flapjack Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackToLab
open Flapjack.Compiler.Backend.StackToLab.ExecutedInput
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem

example : supported (.skip : HolProg 64) = true := by simp [supported, leafSupported]
example : supported (.inst .skip : HolProg 64) = true := by simp [supported, leafSupported]
example : supported (.tick : HolProg 64) = true := by simp [supported, leafSupported]
example : supported (.halt 999 : HolProg 64) = true := by simp [supported, leafSupported]
example : supported (.raise 999 : HolProg 64) = true := by simp [supported, leafSupported]
example : supported (.ret 999 : HolProg 64) = true := by simp [supported, leafSupported]
example : supported (.break 999 : HolProg 64) = true := by simp [supported, leafSupported]
example : supported (.continue 999 : HolProg 64) = true := by simp [supported, leafSupported]
example : supported (.rawCall 999 : HolProg 64) = true := by simp [supported, leafSupported]
example : supported (.jumpLower 2 3 999 : HolProg 64) = true := by simp [supported, leafSupported]
example : supported (.ffi ⟨[]⟩ 2 3 4 5 6 : HolProg 64) = true := by simp [supported, leafSupported]
example : supported (.locValue 2 17 29 : HolProg 64) = true := by simp [supported, leafSupported]
example : supported (.install 2 3 4 5 6 : HolProg 64) = true := by simp [supported, leafSupported]
example : supported (.shMemOp .store8 2 (.addr 3 255) : HolProg 64) = true := by simp [supported, leafSupported]
example : supported (.codeBufferWrite 2 3 : HolProg 64) = true := by simp [supported, leafSupported]
example : supported (.get 2 .endOfHeap : HolProg 64) = false := by simp [supported, leafSupported]
example : sectionToExecuted? (7, (.get 2 .endOfHeap : HolProg 64)) = none := by
  simp [sectionToExecuted?, supported, leafSupported]
example : supported (.set .endOfHeap 2 : HolProg 64) = false := by simp [supported, leafSupported]
example : sectionToExecuted? (7, (.set .endOfHeap 2 : HolProg 64)) = none := by
  simp [sectionToExecuted?, supported, leafSupported]
example : supported (.opCurrHeap .sub 2 3 : HolProg 64) = false := by simp [supported, leafSupported]
example : sectionToExecuted? (7, (.opCurrHeap .sub 2 3 : HolProg 64)) = none := by
  simp [sectionToExecuted?, supported, leafSupported]
example : supported (.alloc 17 : HolProg 64) = false := by simp [supported, leafSupported]
example : sectionToExecuted? (7, (.alloc 17 : HolProg 64)) = none := by
  simp [sectionToExecuted?, supported, leafSupported]
example : supported (.storeConsts 2 3 (some 17) : HolProg 64) = false := by simp [supported, leafSupported]
example : sectionToExecuted? (7, (.storeConsts 2 3 (some 17) : HolProg 64)) = none := by
  simp [sectionToExecuted?, supported, leafSupported]
example : supported (.dataBufferWrite 2 3 : HolProg 64) = false := by simp [supported, leafSupported]
example : sectionToExecuted? (7, (.dataBufferWrite 2 3 : HolProg 64)) = none := by
  simp [sectionToExecuted?, supported, leafSupported]
example : supported (.stackAlloc 17 : HolProg 64) = false := by simp [supported, leafSupported]
example : sectionToExecuted? (7, (.stackAlloc 17 : HolProg 64)) = none := by
  simp [sectionToExecuted?, supported, leafSupported]
example : supported (.stackFree 17 : HolProg 64) = false := by simp [supported, leafSupported]
example : sectionToExecuted? (7, (.stackFree 17 : HolProg 64)) = none := by
  simp [sectionToExecuted?, supported, leafSupported]
example : supported (.stackStore 17 2 : HolProg 64) = false := by simp [supported, leafSupported]
example : sectionToExecuted? (7, (.stackStore 17 2 : HolProg 64)) = none := by
  simp [sectionToExecuted?, supported, leafSupported]
example : supported (.stackStoreAny 2 17 : HolProg 64) = false := by simp [supported, leafSupported]
example : sectionToExecuted? (7, (.stackStoreAny 2 17 : HolProg 64)) = none := by
  simp [sectionToExecuted?, supported, leafSupported]
example : supported (.stackLoad 17 2 : HolProg 64) = false := by simp [supported, leafSupported]
example : sectionToExecuted? (7, (.stackLoad 17 2 : HolProg 64)) = none := by
  simp [sectionToExecuted?, supported, leafSupported]
example : supported (.stackLoadAny 2 17 : HolProg 64) = false := by simp [supported, leafSupported]
example : sectionToExecuted? (7, (.stackLoadAny 2 17 : HolProg 64)) = none := by
  simp [sectionToExecuted?, supported, leafSupported]
example : supported (.stackGetSize 17 : HolProg 64) = false := by simp [supported, leafSupported]
example : sectionToExecuted? (7, (.stackGetSize 17 : HolProg 64)) = none := by
  simp [sectionToExecuted?, supported, leafSupported]
example : supported (.stackSetSize 17 : HolProg 64) = false := by simp [supported, leafSupported]
example : sectionToExecuted? (7, (.stackSetSize 17 : HolProg 64)) = none := by
  simp [sectionToExecuted?, supported, leafSupported]
example : supported (.bitmapLoad 2 17 : HolProg 64) = false := by simp [supported, leafSupported]
example : sectionToExecuted? (7, (.bitmapLoad 2 17 : HolProg 64)) = none := by
  simp [sectionToExecuted?, supported, leafSupported]

-- All four call-option combinations, including the conservative ignored-handler check.
example : supported (.call none (.inl 17) none : HolProg 64) = true := by simp [supported]
example : supported (.call none (.inr 17) (some (.tick, 2, 3)) : HolProg 64) = true := by
  simp [supported, leafSupported]
example : supported (.call (some (.tick, 2, 3, 4)) (.inl 17) none : HolProg 64) = true := by
  simp [supported, leafSupported]
example : supported (.call (some (.tick, 2, 3, 4)) (.inr 17)
    (some (.skip, 5, 6)) : HolProg 64) = true := by simp [supported, leafSupported]
example : supported (.call none (.inl 17) (some (.get 2 .endOfHeap, 3, 4)) : HolProg 64) = false := by
  simp [supported, leafSupported]
example : supported (.call (some (.get 2 .endOfHeap, 3, 4, 5)) (.inl 17) none : HolProg 64) = false := by
  simp [supported, leafSupported]
example : supported (.call (some (.tick, 2, 3, 4)) (.inr 17)
    (some (.loop (.get 5 .endOfHeap), 6, 7)) : HolProg 64) = false := by
  simp [supported, leafSupported]
example : supported (.seq .tick (.get 2 .endOfHeap) : HolProg 64) = false := by
  simp [supported, leafSupported]
example : supported (.seq (.get 2 .endOfHeap) .tick : HolProg 64) = false := by
  simp [supported, leafSupported]
example : supported (.ite .equal 2 (.reg 3) .tick (.get 4 .endOfHeap) : HolProg 64) = false := by
  simp [supported, leafSupported]
example : supported (.ite .equal 2 (.reg 3) (.get 4 .endOfHeap) .tick : HolProg 64) = false := by
  simp [supported, leafSupported]
example : supported (.loop (.get 2 .endOfHeap) : HolProg 64) = false := by
  simp [supported, leafSupported]

-- Four complete original fallback observations; guarded output instead rejects.
example : flattenHOL true (.get 2 .endOfHeap : HolProg 64) 7 2 [] [] = (.list [], false, 2) := by
  simp [flattenHOL]
example : flattenHOL true (.alloc 17 : HolProg 64) 7 2 [] [] = (.list [], false, 2) := by
  simp [flattenHOL]
example : flattenHOL true (.stackStore 17 2 : HolProg 64) 7 2 [] [] = (.list [], false, 2) := by
  simp [flattenHOL]
example : flattenHOL true (.dataBufferWrite 2 3 : HolProg 64) 7 2 [] [] = (.list [], false, 2) := by
  simp [flattenHOL]

-- Exact original whole sections, including absence of redundant entry labels.
example : sectionToExecuted? (7, (.skip : HolProg 64)) =
    some { name := 7, lines := [.label 7 1 0] } := by
  simp [sectionToExecuted?, supported, leafSupported, progToSectionHOL, flattenHOL,
    isSeqHOL, Flapjack.Compiler.Backend.StackAlloc.nextLab, appListAppend, appendAux,
    ExecutedCodec.sectionToExecuted?, ExecutedCodec.mapCodec?, ExecutedCodec.lineToExecuted?]
example : sectionToExecuted? (7, (.seq .tick .skip : HolProg 64)) =
    some { name := 7, lines := [.asm .tick [] 0, .label 7 1 0, .label 7 2 0] } := by
  simp [sectionToExecuted?, supported, leafSupported, progToSectionHOL, flattenHOL,
    isSeqHOL, Flapjack.Compiler.Backend.StackAlloc.nextLab, appListAppend, appendAux,
    ExecutedCodec.sectionToExecuted?, ExecutedCodec.mapCodec?, ExecutedCodec.lineToExecuted?,
    ExecutedCodec.plainToExecuted?, ExecutedCodec.asmToExecuted?, ExecutedCodec.instToExecuted?]
example : sectionToExecuted? (7, (.locValue 2 17 29 : HolProg 64)) =
    some { name := 7, lines := [.labAsm (.locValue 2 ⟨17, 29⟩) [] 0, .label 7 1 0] } := by
  simp [sectionToExecuted?, supported, leafSupported, progToSectionHOL, flattenHOL,
    isSeqHOL, Flapjack.Compiler.Backend.StackAlloc.nextLab, appListAppend, appendAux,
    ExecutedCodec.sectionToExecuted?, ExecutedCodec.mapCodec?, ExecutedCodec.lineToExecuted?,
    ExecutedCodec.labAsmToExecuted, ExecutedCodec.refToExecuted]

-- The residual guard does not pretend the executed codec supports overflow/FP.
example : supported (.inst (.arith (.addOverflow 1 2 3 4)) : HolProg 64) = true := by
  simp [supported, leafSupported]
example : sectionToExecuted? (7, (.inst (.arith (.addOverflow 1 2 3 4)) : HolProg 64)) = none := by
  simp [sectionToExecuted?, supported, leafSupported, progToSectionHOL, flattenHOL,
    isSeqHOL, Flapjack.Compiler.Backend.StackAlloc.nextLab, appListAppend, appendAux,
    ExecutedCodec.sectionToExecuted?, ExecutedCodec.mapCodec?, ExecutedCodec.lineToExecuted?,
    ExecutedCodec.plainToExecuted?, ExecutedCodec.asmToExecuted?, ExecutedCodec.instToExecuted?,
    ExecutedCodec.arithToExecuted?]
example : sectionToExecuted? (7, (.skip : HolProg 1)) =
    some { name := 7, lines := [.label 7 1 0] } := by
  simp [sectionToExecuted?, supported, leafSupported, progToSectionHOL, flattenHOL,
    isSeqHOL, Flapjack.Compiler.Backend.StackAlloc.nextLab, appListAppend, appendAux,
    ExecutedCodec.sectionToExecuted?, ExecutedCodec.mapCodec?, ExecutedCodec.lineToExecuted?]
example : supported (.inst (.const 999 (BitVec.ofNat 80 (2 ^ 79 + 1))) : HolProg 80) = true := by
  simp [supported, leafSupported]

end Flapjack.Test.StackToLabExecutedInput
