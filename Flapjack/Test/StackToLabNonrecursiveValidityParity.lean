import Flapjack.Compiler.Backend.StackToLab.Proofs.Encoding.Nonrecursive
namespace Flapjack.Test.StackToLabNonrecursiveValidityParity
open Flapjack Flapjack.Compiler.Backend.StackToLab
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm

-- Generic full-case applications retain the actual original hypotheses.
example {width : Nat} [NeZero width]
    (tail : Bool) (instruction : HolInst width) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (valid : stackAsmOkExact config (.inst instruction))
    (result : flattenHOL tail (.inst instruction) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreInst tail instruction sectionId next conts breaks lines done nextAfter config _zero valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (register : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (valid : stackAsmOkExact config (.raise register))
    (result : flattenHOL tail (.raise register) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreRaise tail register sectionId next conts breaks lines done nextAfter config _zero valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (register : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (valid : stackAsmOkExact config (.ret register))
    (result : flattenHOL tail (.ret register) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreReturn tail register sectionId next conts breaks lines done nextAfter config _zero valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (left right : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (valid : stackAsmOkExact config (.codeBufferWrite left right))
    (result : flattenHOL tail (.codeBufferWrite left right) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreCodeBufferWrite tail left right sectionId next conts breaks lines done nextAfter config _zero valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (operator : HolMemop) (register : Nat) (address : HolAddr width) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (valid : stackAsmOkExact config (.shMemOp operator register address))
    (result : flattenHOL tail (.shMemOp operator register address) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreSharedMemory tail operator register address sectionId next conts breaks lines done nextAfter config _zero valid result

example {width : Nat} [NeZero width]
    (tail : Bool)  (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.tick))
    (result : flattenHOL tail (.tick) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreTick tail sectionId next conts breaks lines done nextAfter config _zero _valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (register : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.halt register))
    (result : flattenHOL tail (.halt register) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreHalt tail register sectionId next conts breaks lines done nextAfter config _zero _valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (index : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.break index))
    (result : flattenHOL tail (.break index) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreBreak tail index sectionId next conts breaks lines done nextAfter config _zero _valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (index : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.continue index))
    (result : flattenHOL tail (.continue index) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreContinue tail index sectionId next conts breaks lines done nextAfter config _zero _valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (target : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.rawCall target))
    (result : flattenHOL tail (.rawCall target) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreRawCall tail target sectionId next conts breaks lines done nextAfter config _zero _valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (left right target : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.jumpLower left right target))
    (result : flattenHOL tail (.jumpLower left right target) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreJumpLower tail left right target sectionId next conts breaks lines done nextAfter config _zero _valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (name : Flapjack.Basis.Pure.MlString.MlString) (a1 a2 a3 a4 link : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.ffi name a1 a2 a3 a4 link))
    (result : flattenHOL tail (.ffi name a1 a2 a3 a4 link) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreFfi tail name a1 a2 a3 a4 link sectionId next conts breaks lines done nextAfter config _zero _valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (register label entry : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.locValue register label entry))
    (result : flattenHOL tail (.locValue register label entry) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreLocValue tail register label entry sectionId next conts breaks lines done nextAfter config _zero _valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (a1 a2 a3 a4 link : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.install a1 a2 a3 a4 link))
    (result : flattenHOL tail (.install a1 a2 a3 a4 link) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreInstall tail a1 a2 a3 a4 link sectionId next conts breaks lines done nextAfter config _zero _valid result

example {width : Nat} [NeZero width]
    (tail : Bool)  (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.skip))
    (result : flattenHOL tail (.skip) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreSkip tail sectionId next conts breaks lines done nextAfter config _zero _valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (destination : Nat) (store : StoreName) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.get destination store))
    (result : flattenHOL tail (.get destination store) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreGet tail destination store sectionId next conts breaks lines done nextAfter config _zero _valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (store : StoreName) (source : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.set store source))
    (result : flattenHOL tail (.set store source) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreSet tail store source sectionId next conts breaks lines done nextAfter config _zero _valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (operator : HolBinop) (destination source : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.opCurrHeap operator destination source))
    (result : flattenHOL tail (.opCurrHeap operator destination source) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreOpCurrHeap tail operator destination source sectionId next conts breaks lines done nextAfter config _zero _valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (words : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.alloc words))
    (result : flattenHOL tail (.alloc words) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreAlloc tail words sectionId next conts breaks lines done nextAfter config _zero _valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (source bitmap : Nat) (stub : Option Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.storeConsts source bitmap stub))
    (result : flattenHOL tail (.storeConsts source bitmap stub) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreStoreConsts tail source bitmap stub sectionId next conts breaks lines done nextAfter config _zero _valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (address value : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.dataBufferWrite address value))
    (result : flattenHOL tail (.dataBufferWrite address value) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreDataBufferWrite tail address value sectionId next conts breaks lines done nextAfter config _zero _valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (words : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.stackAlloc words))
    (result : flattenHOL tail (.stackAlloc words) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreStackAlloc tail words sectionId next conts breaks lines done nextAfter config _zero _valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (words : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.stackFree words))
    (result : flattenHOL tail (.stackFree words) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreStackFree tail words sectionId next conts breaks lines done nextAfter config _zero _valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (offset register : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.stackStore offset register))
    (result : flattenHOL tail (.stackStore offset register) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreStackStore tail offset register sectionId next conts breaks lines done nextAfter config _zero _valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (register offsetRegister : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.stackStoreAny register offsetRegister))
    (result : flattenHOL tail (.stackStoreAny register offsetRegister) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreStackStoreAny tail register offsetRegister sectionId next conts breaks lines done nextAfter config _zero _valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (offset register : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.stackLoad offset register))
    (result : flattenHOL tail (.stackLoad offset register) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreStackLoad tail offset register sectionId next conts breaks lines done nextAfter config _zero _valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (register offsetRegister : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.stackLoadAny register offsetRegister))
    (result : flattenHOL tail (.stackLoadAny register offsetRegister) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreStackLoadAny tail register offsetRegister sectionId next conts breaks lines done nextAfter config _zero _valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (register : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.stackGetSize register))
    (result : flattenHOL tail (.stackGetSize register) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreStackGetSize tail register sectionId next conts breaks lines done nextAfter config _zero _valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (register : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.stackSetSize register))
    (result : flattenHOL tail (.stackSetSize register) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreStackSetSize tail register sectionId next conts breaks lines done nextAfter config _zero _valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (destination address : Nat) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (_valid : stackAsmOkExact config (.bitmapLoad destination address))
    (result : flattenHOL tail (.bitmapLoad destination address) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreBitmapLoad tail destination address sectionId next conts breaks lines done nextAfter config _zero _valid result

example {width : Nat} [NeZero width]
    (tail : Bool) (target : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat)) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (_zero : asmByteOffsetOkExact config 0 = true)
    (valid : stackAsmOkExact config (.call none target handler))
    (result : flattenHOL tail (.call none target handler) sectionId next conts breaks =
      (lines, done, nextAfter)) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreTailCall tail target handler sectionId next conts breaks lines done nextAfter config _zero valid result

private def cfg : AsmConfigExact 8 where
  isa := .riscv
  encode := fun _ => []
  bigEndian := false
  codeAlignment := 2
  linkReg := none
  avoidRegs := [3]
  regCount := 8
  fpRegCount := 4
  twoRegArith := true
  validImm := fun _ _ => true
  addrOffset := (0,100)
  hwOffset := (0,100)
  byteOffset := (0,100)
  jumpOffset := (0,100)
  cjumpOffset := (0,100)
  locOffset := (0,100)

-- Actual source-valid Cbw and Load instances use the complete case theorem.
example : ∀ line ∈ appListAppend (.list [.asm (.cbw 1 2) [] 0] : AppList (LabLineHOL 8)),
    lineOkPreHOL cfg line := by
  exact flattenLineOkPreCodeBufferWrite false 1 2 7 2 [] [] _ false 2 cfg
    (by decide +kernel)
    (by simp only [stackAsmOkExact]; decide +kernel)
    (by simp [flattenHOL])
example : ∀ line ∈ appListAppend
    (.list [.asm (.shareMem .load 2 (.addr 4 0)) [] 0] : AppList (LabLineHOL 8)),
    lineOkPreHOL cfg line := by
  exact flattenLineOkPreSharedMemory false .load 2 (.addr 4 0) 7 2 [] [] _ false 2 cfg
    (by decide +kernel)
    (by simp only [stackAsmOkExact]; constructor <;> decide +kernel)
    (by simp [flattenHOL])

end Flapjack.Test.StackToLabNonrecursiveValidityParity
