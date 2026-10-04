import Flapjack.Compiler.Backend.WordToStack.NativeCallArgs

/-! Native handler-frame lowering for the literal Word-to-Stack compiler.
The source perf branch is retained as syntax, including the original x64
instrumentation. This establishes representation transport, not handler
simulation or verification of that instrumentation or a production route.
-/
namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Literal handler argument frame; both f and f-prime gain the source slots. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def stackHandlerArgsNative {width : Nat} [NeZero width] {α β : Type}
    (perf : Bool) (dest : Sum α β) (argCount : Nat) (kf : Nat × Nat × Nat) :
    HolProg width :=
  stackArgsNative dest argCount
    (kf.1, kf.2.1 + WordToStack.handlerSlots perf,
      kf.2.2 + WordToStack.handlerSlots perf)

/-- Literal handler restoration/freeing before the arbitrary native continuation.
The two unused frame fields retain independent HOL type variables. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def popHandlerNative {width : Nat} [NeZero width] {β γ : Type}
    (perf : Bool) (kf : Nat × β × γ) (prog : HolProg width) : HolProg width :=
  .seq (.stackLoad kf.1 2)
    (.seq (.set .handler kf.1)
      (.seq (.stackFree (WordToStack.handlerSlots perf)) prog))

/-- Literal allocation, saved handler/labels and optional perf register slots.
Both unused frame fields remain independently polymorphic, as in HOL. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def pushHandlerNative {width : Nat} [NeZero width] {β γ : Type}
    (perf : Bool) (l1 l2 : Nat) (kf : Nat × β × γ) : HolProg width :=
  .seq (.stackAlloc (Flapjack.Compiler.Backend.WordToStack.handlerSlots perf))
    (.seq (.inst (.const kf.1 (1 : BitVec width)))
      (.seq (.stackStore kf.1 0)
        (.seq (.locValue kf.1 l1 l2)
          (.seq (.stackStore kf.1 1)
            (.seq (.get kf.1 .handler)
              (.seq (.stackStore kf.1 2)
                (.seq
                  (if perf then
                    Flapjack.Compiler.Backend.StackLang.listSeq
                      [ .inst (.arith (.binop .or kf.1
                          (Flapjack.Compiler.Backend.WordToStack.perfRsp)
                          (.reg (Flapjack.Compiler.Backend.WordToStack.perfRsp)))),
                        .stackStore kf.1 3,
                        .inst (.arith (.binop .or kf.1
                          (Flapjack.Compiler.Backend.WordToStack.perfRbp)
                          (.reg (Flapjack.Compiler.Backend.WordToStack.perfRbp)))),
                        .stackStore kf.1 4 ]
                  else .skip)
                  (.seq (.stackGetSize kf.1)
                        (.set .handler kf.1)))))))))

/-- Flapjack-only all-input argument frame representation transport. -/
theorem toGeneric_stackHandlerArgsNative {width : Nat} [NeZero width] {α β : Type}
    (perf : Bool) (dest : Sum α β) (argCount : Nat) (kf : Nat × Nat × Nat) :
    toGeneric (stackHandlerArgsNative perf dest argCount kf) =
      WordToStackRegFormat.stackHandlerArgs (α := BitVec width) perf dest argCount kf := by
  exact toGeneric_stackArgsNative dest argCount _

/-- Flapjack-only transport with arbitrary continuation; no evaluation premise. -/
theorem toGeneric_popHandlerNative {width : Nat} [NeZero width] {β γ : Type}
    (perf : Bool) (kf : Nat × β × γ) (prog : HolProg width) :
    toGeneric (popHandlerNative perf kf prog) =
      WordToStackRegFormat.popHandler perf kf (toGeneric prog) := by
  simp [popHandlerNative, WordToStackRegFormat.popHandler, toGeneric, Prog.map]

/-- Flapjack-only transport of both perf alternatives on every positive width.
There is no HOL original for this representation codec equality. -/
theorem toGeneric_pushHandlerNative {width : Nat} [NeZero width] {β γ : Type}
    (perf : Bool) (l1 l2 : Nat) (kf : Nat × β × γ) :
    toGeneric (pushHandlerNative (width := width) perf l1 l2 kf) =
      WordToStackRegFormat.pushHandlerW perf l1 l2 kf := by
  cases perf <;> simp [pushHandlerNative, WordToStackRegFormat.pushHandlerW,
    toGeneric, Prog.map, listSeq, HolInst.toWordLangInst, HolArith.toWordLangArith,
    HolRegImm.toWordRegImm]

/-- Flapjack-only erasure certificate: changing either unused frame field,
including its carrier, leaves the entire native handler setup unchanged.
There is no corresponding named HOL theorem. -/
theorem pushHandlerNative_unusedFrameFields {width : Nat} [NeZero width]
    {β γ δ ε : Type} (perf : Bool) (l1 l2 k : Nat)
    (f : β) (f' : γ) (g : δ) (g' : ε) :
    pushHandlerNative (width := width) perf l1 l2 (k, f, f') =
      pushHandlerNative perf l1 l2 (k, g, g') := rfl

/-- Flapjack-only erasure certificate for the complete restore/free sequence
and arbitrary continuation; there is no named HOL original. -/
theorem popHandlerNative_unusedFrameFields {width : Nat} [NeZero width]
    {β γ δ ε : Type} (perf : Bool) (k : Nat) (prog : HolProg width)
    (f : β) (f' : γ) (g : δ) (g' : ε) :
    popHandlerNative perf (k, f, f') prog =
      popHandlerNative perf (k, g, g') prog := rfl

end Flapjack.Compiler.Backend.WordToStack.Native
