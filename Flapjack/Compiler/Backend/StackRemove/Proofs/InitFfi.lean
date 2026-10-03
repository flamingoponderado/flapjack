import Flapjack.Compiler.Backend.StackRemove.Proofs.InitAny
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitClock
import Flapjack.Compiler.Backend.StackProps.EvaluateNeutral

/-! FFI neutrality of the StackRemove initializer, `stack_removeProofScript.sml`
(3893-3902, 4088-4098).
-/

namespace Flapjack.Compiler.Backend.StackRemove.Proofs.InitFfi
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs.InitMake

/-- Canonical roundtrip for the imported actual state carrier; representation
infrastructure rather than an assumption about any initializer run. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness

/-- Complete original FFI observation of the initializer: replacing the input
FFI state replaces the output FFI state and leaves the result unchanged. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "evaluate_init_code_ffi"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateInitCodeFfi {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap pointer : Nat) (s t : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (c : HolFfiState F)
    (run : StackSemEvaluate.evaluate (initCode generateGc maxHeap pointer, s) = (result, t)) :
    StackSemEvaluate.evaluate (initCode generateGc maxHeap pointer, {s with ffi := c}) =
      (result, {t with ffi := c}) :=
  Compiler.Backend.StackProps.EvaluateNeutral.evaluateFfiNeutral _ s t result c
    ⟨run, InitClock.initCodeClockNeutral generateGc maxHeap pointer⟩

/-- Complete original law: the total initialized state keeps the input FFI
state. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "make_init_any_ffi"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem makeInitAnyFfi {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (code : Spt (HolProg width)) (s : StackSemStateFiniteExact width C F) :
    (makeInitAny generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer code s).ffi =
      s.ffi := by
  unfold makeInitAny
  cases h : makeInitOpt generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer code s with
  | none => rfl
  | some t =>
    simp only
    unfold makeInitOpt at h
    revert h
    cases run : StackSemEvaluate.evaluate (initCode generateGc maxHeap pointer, s) with
    | mk result post =>
      cases result with
      | some r => simp
      | none =>
        simp only
        split
        · intro h
          cases h
          have same := evaluateInitCodeFfi generateGc maxHeap pointer s post none s.ffi run
          have selfUpdate : ({s with ffi := s.ffi} : StackSemStateFiniteExact width C F) = s := rfl
          rw [selfUpdate, run] at same
          have := congrArg (fun x => x.2.ffi) same
          simpa [InitReduce.initReduce] using this
        · simp

end Flapjack.Compiler.Backend.StackRemove.Proofs.InitFfi
