import Flapjack.Compiler.Backend.WordToStack.NativeCompile

namespace Flapjack.Test.WordToStackNativeCompileParity
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm

private def bs : AppList (BitVec 64) × Nat := (.list [4], 1)

-- Original direct comp_skip=T.
example (c : AsmConfigExact 64) : compNative c false .skip bs (4,0,0) = (.skip, bs) := by
  simp [compNative]
-- comp_must=T.
example (c : AsmConfigExact 64) : compNative c false (.mustTerminate .tick) bs (4,0,0) =
    (.tick, bs) := by simp [compNative]
-- comp_seq=T.
example (c : AsmConfigExact 64) : compNative c false (.seq .skip .tick) bs (4,0,0) =
    (.seq .skip .tick, bs) := by simp [compNative]
-- comp_loop=T.
example (c : AsmConfigExact 64) : compNative c false (.loop .ln .tick .ln) bs (4,0,0) =
    (.loop .tick, bs) := by simp [compNative]
-- comp_return=T.
example (c : AsmConfigExact 64) : compNative c false (.return 0 []) bs (4,0,0) =
    (.ret 0, bs) := by
  simp [compNative, WordToStackRegFormat.wReg1,
    wStackLoadNative, seqStackFreeNative, WordToStack.skipFree, WordToStack.numStackRet]
-- comp_raise=T.
example (c : AsmConfigExact 64) : compNative c false (.raise 77) bs (4,0,0) =
    (.call none (.inl raiseStubLocation) none, bs) := by simp [compNative]
-- comp_set_bitmap=T.
example (c : AsmConfigExact 64) : compNative c false (.set .bitmapBase (.var 0)) bs (4,0,0) =
    (.skip, bs) := by simp [compNative]
-- comp_set_bad=T.
example (c : AsmConfigExact 64) : compNative c false (.set .currHeap (.const 9)) bs (4,0,0) =
    (.skip, bs) := by simp [compNative]
-- comp_assign_fallback=T.
example (c : AsmConfigExact 64) : compNative c false (.assign 1 (.const 9)) bs (4,0,0) =
    (.skip, bs) := by simp [compNative]
-- comp_install=T.
example (c : AsmConfigExact 64) : compNative c false (.install 2 4 4 6 (.ln,.ln)) bs (4,0,0) =
    (.install 1 2 2 3 0, bs) := by
  simp [compNative, WordToStackRegFormat.wReg1, WordToStackRegFormat.wReg2,
    wStackLoadNative]
-- comp_tailcall=T.
example (c : AsmConfigExact 64) : compNative c false (.call none (some 9) [] none) bs (4,0,0) =
    (.seq .skip (.call none (.inl 9) none), bs) := by
  simp [compNative, callDestNative, seqStackFreeNative, WordToStack.stackFree,
    WordToStack.stackArgCount]
-- comp_share_bad=T.
example (c : AsmConfigExact 64) : compNative c false (.shareInst .load 0 (.const 9)) bs (4,0,0) =
    (.skip, bs) := by simp [compNative, expToAddrHOL]

-- comp_if_valid=T.
example (c : AsmConfigExact 64) :
    compNative {c with validImm := fun _ _ => true} false
      (.ite .equal 0 (.imm 9) .tick .skip) bs (4,0,0) =
      (.ite .equal 0 (.imm 9) .tick .skip, bs) := by
  simp [compNative, WordToStackRegFormat.wReg1, wStackLoadNative]
-- comp_if_materialize=T.
example (c : AsmConfigExact 64) :
    compNative {c with validImm := fun _ _ => false} false
      (.ite .equal 0 (.imm 9) .tick .skip) bs (4,0,0) =
      (.seq (.inst (.const 5 9)) (.ite .equal 0 (.reg 5) .tick .skip), bs) := by
  simp [compNative, WordToStackRegFormat.wReg1, wStackLoadNative]
-- comp_returning=T.
example (c : AsmConfigExact 64) :
    compNative c false (.call (some ([],(.ln,.ln),.tick,7,8)) (some 9) [] none) bs (4,0,0) =
      (.seq .skip (.seq .skip (.seq (.stackAlloc 0)
        (.seq .skip (.call (some (.seq .skip .tick,0,7,8)) (.inl 9) none)))), bs) := by
  simp [compNative, callDestNative, wLiveNative, stackArgsNative, stackMoveNative,
    WordToStack.stackArgCount, copyRetNative, WordToStack.numStackRet]
-- comp_handler=T, recursive handler body is compiled rather than supplied.
example (c : AsmConfigExact 64) :
    compNative c false (.call (some ([],(.ln,.ln),.tick,7,8)) (some 9) []
      (some (99,.seq .tick .skip,11,12))) bs (4,0,0) =
      (.seq .skip (.seq .skip (.seq (pushHandlerNative false 11 12 (4,0,0))
        (.seq (stackHandlerArgsNative false (.inl 9 : Sum Nat Nat) 1 (4,0,0))
          (.seq .skip (.call
            (some (.seq .skip (popHandlerNative false (4,0,0) .tick),0,7,8))
            (.inl 9) (some (.seq .tick .skip,11,12))))))), bs) := by
  simp [compNative, callDestNative, wLiveNative, copyRetNative, WordToStack.numStackRet]
-- comp_seq_bitmaps=T: second allocation uses the first returned bitmap.
example (c : AsmConfigExact 64) :
    (compNative c false (.seq (.alloc 0 (.ln,.ln)) (.alloc 0 (.ln,.ln))) bs (4,1,2)).2.2 = 3 := by
  simp [compNative, wLiveNative, WordToStack.insertBitmap, WordToStack.writeBitmapExact,
    WordToStack.wordListW, bs]
-- comp_if_bitmaps=T: both branches are compiled in source order.
example (c : AsmConfigExact 64) :
    (compNative {c with validImm := fun _ _ => true} false
      (.ite .equal 0 (.imm 9) (.alloc 0 (.ln,.ln)) (.alloc 0 (.ln,.ln))) bs (4,1,2)).2.2 = 3 := by
  simp [compNative, wLiveNative, WordToStack.insertBitmap, WordToStack.writeBitmapExact,
    WordToStack.wordListW, bs]
-- comp_call_bitmaps=T: live frame, return body, then handler body insert.
example (c : AsmConfigExact 64) :
    (compNative c false (.call (some ([],(.ln,.ln),.alloc 0 (.ln,.ln),7,8))
      (some 9) [] (some (99,.alloc 0 (.ln,.ln),11,12))) bs (4,1,2)).2.2 = 4 := by
  simp [compNative, wLiveNative, WordToStack.insertBitmap, WordToStack.writeBitmapExact,
    WordToStack.wordListW, bs]

end Flapjack.Test.WordToStackNativeCompileParity
