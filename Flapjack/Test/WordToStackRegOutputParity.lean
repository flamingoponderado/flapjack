import Flapjack.Compiler.Backend.WordToStack.NativeCompile

namespace Flapjack.Test.WordToStackRegOutputParity
open Flapjack Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

/- Six independent original `comp` EVAL output tuples from
word_to_stack_reg_output_probe.out. These compare the complete target program
and bitmap accumulator/index directly, without any register-bound theorem.
HOL stackLang's `const_inst r w` is the printed overload `Inst (Const r w)`
(stackLangScript.sml:82), translated literally below. Config is arbitrary:
these selected cases do not inspect config; no config validity is assumed. -/
private abbrev live : Spt Unit × Spt Unit := (.ln, sptInsert 32 () .ln)
private abbrev initial : AppList (BitVec 64) × Nat :=
  (.append (.list [4]) (.list [7]), 17)
private abbrev bs1 : AppList (BitVec 64) × Nat :=
  (.append initial.1 (.list [513]), 18)
private abbrev bs2 : AppList (BitVec 64) × Nat :=
  (.append bs1.1 (.list [513]), 19)
private abbrev liveCode (idx : Nat) : HolProg 64 :=
  .seq (.inst (.const 4 (BitVec.ofNat 64 idx))) (.stackStore 4 0)
private abbrev allocCode (idx : Nat) : HolProg 64 := .seq (liveCode idx) (.alloc 1)
private abbrev getCode : HolProg 64 := .seq (.get 4 .currHeap) (.stackStore 4 0)

-- rbo_must_alloc
example (conf : AsmConfigExact 64) :
    compNative conf false (.mustTerminate (.seq (.alloc 2 live) (.get 80 .currHeap)))
      initial (4,7,9) = (.seq (allocCode 18) getCode, bs1) := by cbv

-- rbo_loop_if_reg
example (conf : AsmConfigExact 64) :
    compNative conf false (.loop (sptInsert 32 () .ln)
      (.ite .equal 80 (.reg 82) (.alloc 2 live) (.get 80 .currHeap))
      (sptInsert 34 () .ln)) initial (4,7,9) =
    (.loop (.seq (.stackLoad 4 0) (.seq (.stackLoad 5 0)
      (.ite .equal 4 (.reg 5) (allocCode 18) getCode))), bs1) := by cbv

-- rbo_seq_loops
example (conf : AsmConfigExact 64) :
    compNative conf false (.seq (.loop .ln (.alloc 2 live) .ln)
      (.loop .ln (.get 80 .currHeap) .ln)) initial (4,7,9) =
    (.seq (.loop (allocCode 18)) (.loop getCode), bs1) := by cbv

-- rbo_tail_indirect
example (conf : AsmConfigExact 64) :
    compNative conf false (.call none none [0,2,4,6,8,10] none) initial (4,7,9) =
    (.seq (.seq (.stackLoad 5 5) .skip)
      (.seq (.stackFree 6) (.call none (.inr 5) none)), initial) := by cbv

-- rbo_return_direct
example (conf : AsmConfigExact 64) :
    compNative conf false (.call (some ([2,4],live,.get 80 .currHeap,7,9))
      (some 11) [2,4,6,8,10] none) initial (4,7,9) =
    (.seq .skip (.seq (liveCode 18)
      (.seq (.seq (.seq (.stackAlloc 2) (.seq (.stackLoad 4 8) (.stackStore 4 1)))
        (.seq (.stackLoad 4 7) (.stackStore 4 0)))
        (.seq .skip (.call (some (.seq .skip getCode,0,7,9)) (.inl 11) none)))), bs1) := by cbv

private abbrev push : HolProg 64 :=
  .seq (.stackAlloc 3) (.seq (.inst (.const 4 1))
    (.seq (.stackStore 4 0) (.seq (.locValue 4 70 90)
      (.seq (.stackStore 4 1) (.seq (.get 4 .handler)
        (.seq (.stackStore 4 2) (.seq .skip (.seq (.stackGetSize 4) (.set .handler 4)))))))))
private abbrev pop : HolProg 64 :=
  .seq (.stackLoad 4 2) (.seq (.set .handler 4)
    (.seq (.stackFree 3) (.loop (allocCode 19))))

-- rbo_handler_indirect
example (conf : AsmConfigExact 64) :
    compNative conf false (.call (some ([2,4],live,.loop .ln (.alloc 2 live) .ln,7,9))
      none [2,4,6,8,10] (some (2,.mustTerminate (.get 80 .currHeap),70,90)))
      initial (4,7,9) =
    (.seq (.seq (.stackLoad 5 5) .skip) (.seq (liveCode 18)
      (.seq push (.seq (.seq (.stackAlloc 1) (.seq (.stackLoad 4 10) (.stackStore 4 0)))
        (.seq .skip (.call (some (.seq .skip pop,0,7,9)) (.inr 5)
          (some (getCode,70,90))))))), bs2) := by cbv

end Flapjack.Test.WordToStackRegOutputParity
