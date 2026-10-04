import Flapjack.Compiler.Backend.WordToStack.NativeMoves
import Flapjack.Compiler.Backend.WordToStack.NativeReturn
import Flapjack.Compiler.Backend.WordToStack.NativeCallArgs
import Flapjack.Compiler.Backend.WordToStack.NativeHandlers
import Flapjack.Compiler.Backend.WordToStack.NativePerf
import Flapjack.Compiler.Backend.WordToStack.NativeSharedMemory
import Flapjack.Compiler.Backend.WordToStack.NativeLive

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open WordToStackRegFormat (wReg1 wReg2)

/-- Flapjack-only constructor translation between the two exact store-name
mirrors. It preserves the fixed five-bit Temp field and has no HOL original. -/
def storeNameOfWord : WordStoreHOL → StoreName
  | .temp n => .temp n
  | .nextFree => .nextFree
  | .endOfHeap => .endOfHeap
  | .triggerGC => .triggerGC
  | .heapLength => .heapLength
  | .progStart => .progStart
  | .bitmapBase => .bitmapBase
  | .currHeap => .currHeap
  | .otherHeap => .otherHeap
  | .allocSize => .allocSize
  | .globals => .globals
  | .globReal => .globReal
  | .handler => .handler
  | .genStart => .genStart
  | .codeBuffer => .codeBuffer
  | .codeBufferEnd => .codeBufferEnd
  | .bitmapBuffer => .bitmapBuffer
  | .bitmapBufferEnd => .bitmapBufferEnd

/-- Complete literal source traversal. Both recursive continuations and all
bitmap components are compiled in source order. The exact assembler config
and word dimension are retained; production routing and correctness remain open. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def compNative {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (perf : Bool) (program : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (kf : Nat × Nat × Nat) :
    HolProg width × (AppList (BitVec width) × Nat) :=
  match program with
  | .skip => (.skip, bs)
  | .move _ xs => (wMoveNative xs kf, bs)
  | .inst i => (wInstNative (HolInst.ofWordLangInst i) kf, bs)
  | .return v vs =>
      let (xs, r) := wReg1 v kf
      (wStackLoadNative xs (seqStackFreeNative (WordToStack.skipFree kf.1 kf.2.1 kf.2.2 vs)
        (.ret r)), bs)
  | .raise _ => (.call none (.inl raiseStubLocation) none, bs)
  | .opCurrHeap op dst src =>
      let (xs, r) := wReg1 src kf
      (wStackLoadNative xs (wRegWrite1Native (fun d => .opCurrHeap op d r) dst kf), bs)
  | .tick => (.tick, bs)
  | .break k => (.break k, bs)
  | .continue k => (.continue k, bs)
  | .mustTerminate p => compNative conf perf p bs kf
  | .seq first second =>
      let (q1, bs) := compNative conf perf first bs kf
      let (q2, bs) := compNative conf perf second bs kf
      (.seq q1 q2, bs)
  | .ite cmp r ri first second =>
      let (xs, r) := wReg1 r kf
      let (q1, bs) := compNative conf perf first bs kf
      let (q2, bs) := compNative conf perf second bs kf
      match ri with
      | .reg n =>
          let (ys, n) := wReg2 n kf
          (wStackLoadNative (xs ++ ys) (.ite cmp r (.reg n) q1 q2), bs)
      | .imm i =>
          if conf.validImm (.inr cmp) i then
            (wStackLoadNative xs (.ite cmp r (.imm i) q1 q2), bs)
          else
            let n := kf.1 + 1
            (.seq (.inst (.const n i)) (wStackLoadNative xs (.ite cmp r (.reg n) q1 q2)), bs)
  | .loop _ p _ =>
      let (q, bs) := compNative conf perf p bs kf
      (.loop q, bs)
  | .set name exp =>
      match name with
      | .bitmapBase => (.skip, bs)
      | _ =>
          match exp with
          | .var n =>
              let (xs, r) := wReg1 n kf
              (wStackLoadNative xs (.set (storeNameOfWord name) r), bs)
          | _ => (.skip, bs)
  | .get n name => (wRegWrite1Native (fun r => .get r (storeNameOfWord name)) n kf, bs)
  | .call ret dest args handler =>
      let (q0, dest) := callDestNative dest args kf
      match ret with
      | none =>
          (.seq q0 (seqStackFreeNative
            (WordToStack.stackFree dest args.length kf.1 kf.2.1 kf.2.2)
            (.call none dest none)), bs)
      | some (vs, live, retCode, l1, l2) =>
          let (q1, bs) := wLiveNative live bs kf
          let (q2, bs) := compNative conf perf retCode bs kf
          let pre := if perf then perfCallPrefixNative l1 l2 kf.1 else .skip
          let suf := if perf then perfCallSuffixNative else .skip
          match handler with
          | none =>
              let q3 := .seq suf (copyRetNative perf false kf vs q2)
              (.seq q0 (.seq q1 (.seq (stackArgsNative dest (args.length + 1) kf)
                (.seq pre (.call (some (q3, 0, l1, l2)) dest none)))), bs)
          | some (_, handleCode, h1, h2) =>
              let q3 := .seq suf (copyRetNative perf true kf vs (popHandlerNative perf kf q2))
              let (q4, bs) := compNative conf perf handleCode bs kf
              (.seq q0 (.seq q1 (.seq (pushHandlerNative perf h1 h2 kf)
                (.seq (stackHandlerArgsNative perf dest (args.length + 1) kf)
                  (.seq pre (.call (some (q3, 0, l1, l2)) dest (some (q4, h1, h2))))))), bs)
  | .alloc _ live =>
      let (q1, bs) := wLiveNative live bs kf
      (.seq q1 (.alloc 1), bs)
  | .storeConsts _ _ _ _ ws =>
      let (newBs, i) := insertBitmap (constWordsToBitmapW ws ws.length) bs
      (.seq (.inst (.const 1 (BitVec.ofNat width i)))
        (.storeConsts kf.1 (kf.1 + 1) (some storeConstsStubLocation)), newBs)
  | .locValue r l => (wRegWrite1Native (fun n => .locValue n l 0) r kf, bs)
  | .install r1 r2 r3 r4 _ =>
      let (xs, r3) := wReg1 r3 kf
      let (ys, r4) := wReg2 r4 kf
      (wStackLoadNative (xs ++ ys) (.install (r1 / 2) (r2 / 2) r3 r4 0), bs)
  | .codeBufferWrite r1 r2 =>
      let (xs, r1) := wReg1 r1 kf
      let (ys, r2) := wReg2 r2 kf
      (wStackLoadNative (xs ++ ys) (.codeBufferWrite r1 r2), bs)
  | .dataBufferWrite r1 r2 =>
      let (xs, r1) := wReg1 r1 kf
      let (ys, r2) := wReg2 r2 kf
      (wStackLoadNative (xs ++ ys) (.dataBufferWrite r1 r2), bs)
  | .ffi i r1 r2 r3 r4 _ => (.ffi i (r1 / 2) (r2 / 2) (r3 / 2) (r4 / 2) 0, bs)
  | .shareInst op v exp =>
      match expToAddrHOL exp with
      | none => (.skip, bs)
      | some addr => (wShareInstNative op v (HolAddr.ofWordLangAddr addr) kf, bs)
  | _ => (.skip, bs)
termination_by sizeOf program

end Flapjack.Compiler.Backend.WordToStack.Native
