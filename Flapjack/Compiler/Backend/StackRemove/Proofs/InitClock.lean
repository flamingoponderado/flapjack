import Flapjack.Compiler.Backend.StackRemove.InitCode
import Flapjack.Compiler.Backend.StackProps.EvaluateNeutral

namespace Flapjack.Compiler.Backend.StackRemove.Proofs.InitClock
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.StackSemEvaluate

/-- Original store-list neutrality, for arbitrary words, registers and aliases.
Only the standard positive-width word carrier differs from HOL. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml"
  "clock_neutral_store_list_code" (words_as_type_indexed_bitvec)]
theorem clockNeutralStoreListCode {width : Nat} [NeZero width]
    (values : List (Sum (BitVec width) Nat)) (address temporary : Nat) :
    clockNeutralHOL (storeListCode address temporary values) := by
  induction values with
  | nil => simp [storeListCode, clockNeutralHOL]
  | cons value rest ih =>
    cases value <;>
      simp [storeListCode, listSeqHOL, addBytesInWordInst, clockNeutralHOL, ih]

/-- Flapjack factoring of the original initializer's structural neutrality.
It introduces no program, register, heap or successful-evaluation premise. -/
theorem initCodeClockNeutral {width : Nat} [NeZero width]
    (generateGc : Bool) (maximumHeap pointer : Nat) :
    clockNeutralHOL (initCode (width := width) generateGc maximumHeap pointer) := by
  simp [initCode, initMemory, listSeqHOL, clockNeutralHOL, moveHOL,
    subInst, addInst, rightShiftInst, leftShiftInst, constInst, loadInst,
    storeInst, addBytesInWordInst, clockNeutralStoreListCode]

/-- Canonical imported state roundtrip, used only to identify the reviewed
finite-map representation of the actual evaluator's state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness

/-- Full original local initializer clock observation. The sole premise is
the actual source evaluation; replacement-clock execution is proved. The
native evaluator inherits reals_as_rational_cuts (SOUNDNESS item 8), with no
new floating-point correspondence claim. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml"
  "evaluate_init_code_clock" (fmap_as_finite_support := [regs, fpRegs, store])
  (words_as_type_indexed_bitvec)]
theorem evaluateInitCodeClock {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maximumHeap pointer : Nat)
    (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (clock : Nat)
    (run : evaluate (initCode generateGc maximumHeap pointer, source) = (result, post)) :
    evaluate (initCode generateGc maximumHeap pointer, {source with clock := clock}) =
      (result, {post with clock := clock}) :=
  EvaluateNeutral.evaluateClockNeutral _ source post result clock
    ⟨run, initCodeClockNeutral generateGc maximumHeap pointer⟩

end Flapjack.Compiler.Backend.StackRemove.Proofs.InitClock
