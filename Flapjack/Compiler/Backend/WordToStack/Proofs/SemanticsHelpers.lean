import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRel
import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef

namespace Flapjack.WordToStackProofs.SemanticsHelpers
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang

/-- Canonical source-state relation codec re-export; no separate HOL original. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Canonical target-state relation codec re-export; no separate HOL original. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

namespace WordCallWitnesses
/-- Canonical WordSem codec re-export for the evaluator's map translation. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end WordCallWitnesses
namespace StackCallWitnesses
/-- Canonical StackSem codec re-export for the evaluator's map translation. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness
end StackCallWitnesses

/-- Full original synchronized-clock replacement, retaining arbitrary extra
stack offset and all other state-relation conjuncts. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stateRelWithClock {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (registerCount clock : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat) (extra : Nat)
    (related : stateRel ac registerCount 0 0 source target lens extra) :
    stateRel ac registerCount 0 0 {source with clock := clock} {target with clock := clock} lens extra := by
  unfold stateRel at related ⊢
  exact ⟨rfl, related.2⟩

/-- Full original WordSem tail-call result exclusion. Arbitrary destination,
argument list and handler are retained; the sole premise is native execution.
The evaluator closure inherits reals_as_rational_cuts; no FP correspondence is asserted. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordCallNoneNotBreakContinue {width : Nat} [NeZero width] {C F : Type}
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (source post : WordSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (execution : WordSemStateFiniteExact.evaluate (.call none dest args handler) source = (result, post)) :
    (∀ n, result ≠ some (.break n)) ∧ (∀ n, result ≠ some (.continue n)) := by
  rw [WordSemStateFiniteExact.evaluate] at execution
  repeat' (first | split at execution | dsimp only at execution)
  all_goals
    obtain ⟨equal, -⟩ := Prod.mk.inj execution
    subst result
    constructor <;> intro n equal <;> simp_all [wordSemBadFunReturn]

/-- Full original StackSem tail-call result exclusion. The sole premise is
actual native evaluation with arbitrary destination and handler. The evaluator
closure inherits reals_as_rational_cuts; no FP correspondence is asserted. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackCallNoneNotBreakContinue {width : Nat} [NeZero width] {C F : Type}
    (dest : Sum Nat Nat) (handler : Option (HolProg width × Nat × Nat))
    (source post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (.call none dest handler, source) = (result, post)) :
    (∀ n, result ≠ some (.break n)) ∧ (∀ n, result ≠ some (.continue n)) := by
  rw [StackSemEvaluate.evaluate_call] at execution
  dsimp only at execution
  repeat' (first | split at execution | dsimp only at execution)
  all_goals
    obtain ⟨equal, -⟩ := Prod.mk.inj execution
    subst result
    constructor <;> intro n equal <;> simp_all [StackSemControl.badFunReturn]

end Flapjack.WordToStackProofs.SemanticsHelpers
