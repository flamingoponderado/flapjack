import Flapjack.Compiler.Backend.StackToLab.Proofs.Encoding.Recursive
import Flapjack.Compiler.Backend.StackToLab.Native
import Flapjack.Compiler.Backend.LabProps.Native
import Flapjack.Compiler.Backend.StackProps.ProgramValidity
namespace Flapjack.Test.StackToLabRecursiveValidityParity
open Flapjack Flapjack.Compiler.Backend.StackToLab
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackToLab.Proofs

example {width : Nat} [NeZero width]
    (tail : Bool) (first second : HolProg width) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (zero : asmByteOffsetOkExact config 0 = true)
    (valid : stackAsmOkExact config (.seq first second))
    (result : flattenHOL tail (.seq first second) sectionId next conts breaks =
      (lines, done, nextAfter))
    (ihFirst : ∀ (t : Bool) (n m : Nat) (cs bs : List Nat)
      (ls : AppList (LabLineHOL width)) (a : Bool) (b : Nat),
      asmByteOffsetOkExact config 0 = true → stackAsmOkExact config first →
      flattenHOL t first n m cs bs = (ls,a,b) →
      ∀ line ∈ appListAppend ls, lineOkPreHOL config line)
    (ihSecond : ∀ (t : Bool) (n m : Nat) (cs bs : List Nat)
      (ls : AppList (LabLineHOL width)) (a : Bool) (b : Nat),
      asmByteOffsetOkExact config 0 = true → stackAsmOkExact config second →
      flattenHOL t second n m cs bs = (ls,a,b) →
      ∀ line ∈ appListAppend ls, lineOkPreHOL config line)
    : ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreSeq tail first second sectionId next conts breaks lines done nextAfter config zero valid result ihFirst ihSecond

example {width : Nat} [NeZero width]
    (tail : Bool) (body : HolProg width) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (zero : asmByteOffsetOkExact config 0 = true)
    (valid : stackAsmOkExact config (.loop body))
    (result : flattenHOL tail (.loop body) sectionId next conts breaks =
      (lines, done, nextAfter))
    (ihBody : ∀ (t : Bool) (n m : Nat) (cs bs : List Nat)
      (ls : AppList (LabLineHOL width)) (a : Bool) (b : Nat),
      asmByteOffsetOkExact config 0 = true → stackAsmOkExact config body →
      flattenHOL t body n m cs bs = (ls,a,b) →
      ∀ line ∈ appListAppend ls, lineOkPreHOL config line) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreLoop tail body sectionId next conts breaks lines done nextAfter config zero valid result ihBody

example {width : Nat} [NeZero width]
    (tail : Bool) (condition : HolCmp) (register : Nat) (right : HolRegImm width)
    (first second : HolProg width) (sectionId next : Nat)
    (conts breaks : List Nat) (lines : AppList (LabLineHOL width))
    (done : Bool) (nextAfter : Nat) (config : AsmConfigExact width)
    (zero : asmByteOffsetOkExact config 0 = true)
    (valid : stackAsmOkExact config (.ite condition register right first second))
    (result : flattenHOL tail (.ite condition register right first second)
      sectionId next conts breaks = (lines, done, nextAfter))
    (ihFirst : ∀ (t : Bool) (n m : Nat) (cs bs : List Nat)
      (ls : AppList (LabLineHOL width)) (a : Bool) (b : Nat),
      asmByteOffsetOkExact config 0 = true → stackAsmOkExact config first →
      flattenHOL t first n m cs bs = (ls,a,b) →
      ∀ line ∈ appListAppend ls, lineOkPreHOL config line)
    (ihSecond : ∀ (t : Bool) (n m : Nat) (cs bs : List Nat)
      (ls : AppList (LabLineHOL width)) (a : Bool) (b : Nat),
      asmByteOffsetOkExact config 0 = true → stackAsmOkExact config second →
      flattenHOL t second n m cs bs = (ls,a,b) →
      ∀ line ∈ appListAppend ls, lineOkPreHOL config line)
    : ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreIf tail condition register right first second sectionId next conts breaks lines done nextAfter config zero valid result ihFirst ihSecond

example {width : Nat} [NeZero width]
    (tail : Bool) (body : HolProg width) (link returnSection returnLabel : Nat)
    (target : Sum Nat Nat) (sectionId next : Nat) (conts breaks : List Nat)
    (lines : AppList (LabLineHOL width)) (done : Bool) (nextAfter : Nat)
    (config : AsmConfigExact width) (zero : asmByteOffsetOkExact config 0 = true)
    (valid : stackAsmOkExact config
      (.call (some (body,link,returnSection,returnLabel)) target none))
    (result : flattenHOL tail
      (.call (some (body,link,returnSection,returnLabel)) target none)
      sectionId next conts breaks = (lines,done,nextAfter))
    (ihBody : ∀ (t : Bool) (n m : Nat) (cs bs : List Nat)
      (ls : AppList (LabLineHOL width)) (a : Bool) (b : Nat),
      asmByteOffsetOkExact config 0 = true → stackAsmOkExact config body →
      flattenHOL t body n m cs bs = (ls,a,b) →
      ∀ line ∈ appListAppend ls, lineOkPreHOL config line) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreReturnedCallNone tail body link returnSection returnLabel target sectionId next conts breaks lines done nextAfter config zero valid result ihBody

example {width : Nat} [NeZero width]
    (tail : Bool) (body : HolProg width) (link returnSection returnLabel : Nat)
    (target : Sum Nat Nat) (handlerBody : HolProg width)
    (handlerSection handlerLabel : Nat) (sectionId next : Nat) (conts breaks : List Nat)
    (lines : AppList (LabLineHOL width)) (done : Bool) (nextAfter : Nat)
    (config : AsmConfigExact width) (zero : asmByteOffsetOkExact config 0 = true)
    (valid : stackAsmOkExact config
      (.call (some (body,link,returnSection,returnLabel)) target (some (handlerBody,handlerSection,handlerLabel))))
    (result : flattenHOL tail
      (.call (some (body,link,returnSection,returnLabel)) target (some (handlerBody,handlerSection,handlerLabel)))
      sectionId next conts breaks = (lines,done,nextAfter))
    (ihBody : ∀ (t : Bool) (n m : Nat) (cs bs : List Nat)
      (ls : AppList (LabLineHOL width)) (a : Bool) (b : Nat),
      asmByteOffsetOkExact config 0 = true → stackAsmOkExact config body →
      flattenHOL t body n m cs bs = (ls,a,b) →
      ∀ line ∈ appListAppend ls, lineOkPreHOL config line)
    (ihHandler : ∀ (t : Bool) (n m : Nat) (cs bs : List Nat)
      (ls : AppList (LabLineHOL width)) (a : Bool) (b : Nat),
      asmByteOffsetOkExact config 0 = true → stackAsmOkExact config handlerBody →
      flattenHOL t handlerBody n m cs bs = (ls,a,b) →
      ∀ line ∈ appListAppend ls, lineOkPreHOL config line) :
    ∀ line ∈ appListAppend lines, lineOkPreHOL config line :=
  flattenLineOkPreReturnedCallSome tail body link returnSection returnLabel target handlerBody handlerSection handlerLabel sectionId next conts breaks lines done nextAfter config zero valid result ihBody ihHandler

end Flapjack.Test.StackToLabRecursiveValidityParity
