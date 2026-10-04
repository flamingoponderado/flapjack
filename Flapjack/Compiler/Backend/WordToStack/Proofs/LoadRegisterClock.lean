import Flapjack.Compiler.Backend.WordToStack.Proofs.LoadRegister

namespace Flapjack.WordToStackProofs.LoadRegisterClock
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackLang

/-- Genuine canonical target codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness



/-- Full original local evaluate_wStackLoad_clock, with explicit canonical map and positive-word qualifications. Unconditional whole-pair equality, including invalid
stack use and out-of-range errors; no supplied run or bound premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateWStackLoadClock {width : Nat} [NeZero width] {C F : Type}
    (loads : List (Nat × Nat)) (target : StackSemStateFiniteExact width C F)
    (clock : Nat) :
    StackSemEvaluate.evaluate (wStackLoadNative loads .skip, {target with clock := clock}) =
      (StackSemEvaluate.evaluate (wStackLoadNative loads .skip, target)).map
        id (fun post => {post with clock := clock}) := by
  induction loads generalizing target with
  | nil => simp [wStackLoadNative, StackSemEvaluate.evaluate_skip]
  | cons entry loads ih =>
    rcases entry with ⟨register, slot⟩
    simp only [wStackLoadNative, StackSemEvaluate.evaluate_seq,
      StackSemEvaluate.evaluate_stackLoad]
    by_cases enabled : target.useStack = true
    · simp only [enabled, Bool.not_true, Bool.false_eq_true, if_false]
      by_cases bound : target.stackSpace + slot < target.stack.length
      · simp only [bound, dif_pos, StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
        simpa [StackSemStateOps.setVar, StackSemControl.fixClock, enabled] using
          ih (StackSemStateOps.setVar register target.stack[target.stackSpace + slot] target)
      · simp [bound, StackSemControl.fixClock, StackSemStateOps.emptyEnv, enabled]
    · simp [enabled, StackSemControl.fixClock]

end Flapjack.WordToStackProofs.LoadRegisterClock
