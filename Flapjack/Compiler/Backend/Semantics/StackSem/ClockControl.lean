import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef
namespace Flapjack.StackSemClockControl
open Flapjack Compiler.Backend.StackLang Compiler.Encoders.Asm
open StackSemEvaluate StackSemControl StackSemStateOps
/-- Canonical imported state roundtrip; Flapjack representation infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Genuine Seq case of the original pre-rebind clock induction. Both source
IHs are retained; the second is guarded by the actual clamped first run. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateClockSeq {width : Nat} [NeZero width] {C F : Type}
    (first second : HolProg width) (source : StackSemStateFiniteExact width C F)
    (_firstIH : ∀ result post, evaluate (first,source) = (result,post) → post.clock ≤ source.clock)
    (secondIH : ∀ firstResult middle,
      fixClock source (evaluate (first,source)) = (firstResult,middle) → firstResult = none →
      ∀ result post, evaluate (second,middle) = (result,post) → post.clock ≤ middle.clock)
    (result : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F)
    (execution : evaluate (.seq first second,source) = (result,post)) : post.clock ≤ source.clock := by
  rw [evaluate_seq] at execution
  rcases firstRun : fixClock source (evaluate (first,source)) with ⟨firstResult,middle⟩
  have bound := fixClockImp source (evaluate (first,source)) firstResult middle firstRun
  rw [firstRun] at execution
  cases firstResult with
  | none => exact Nat.le_trans (secondIH none middle firstRun rfl result post execution) bound
  | some value =>
    have same := (Prod.mk.inj execution).2
    subst post
    exact bound
/-- Genuine If case, with the two original lookup/comparison-guarded IHs. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateClockIf {width : Nat} [NeZero width] {C F : Type}
    (comparison : Cmp) (register : Nat) (operand : HolRegImm width) (first second : HolProg width)
    (source : StackSemStateFiniteExact width C F)
    (firstIH : ∀ left right, getVar register source = some left →
      StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some right →
      wordSemWordCmp comparison left right = some true →
      ∀ result post, evaluate (first,source) = (result,post) → post.clock ≤ source.clock)
    (secondIH : ∀ left right, getVar register source = some left →
      StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some right →
      wordSemWordCmp comparison left right = some false →
      ∀ result post, evaluate (second,source) = (result,post) → post.clock ≤ source.clock)
    (result : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F)
    (execution : evaluate (.ite comparison register operand first second,source) = (result,post)) :
    post.clock ≤ source.clock := by
  rw [evaluate_ite] at execution
  cases leftLookup : getVar register source with
  | none => rw [leftLookup] at execution; have same := (Prod.mk.inj execution).2; subst post; exact Nat.le_refl _
  | some left =>
    rw [leftLookup] at execution
    cases rightLookup : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source with
    | none => rw [rightLookup] at execution; have same := (Prod.mk.inj execution).2; subst post; exact Nat.le_refl _
    | some right =>
      rw [rightLookup] at execution
      simp only [] at execution
      cases compared : wordSemWordCmp comparison left right with
      | none => rw [compared] at execution; have same := (Prod.mk.inj execution).2; subst post; exact Nat.le_refl _
      | some boolean =>
        cases boolean with
        | false => rw [compared] at execution; exact secondIH left right leftLookup rightLookup compared result post execution
        | true => rw [compared] at execution; exact firstIH left right leftLookup rightLookup compared result post execution
/-- Genuine Loop case, retaining the actual body IH and original guarded
reentry IH. No global clock monotonicity premise is introduced. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateClockLoop {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (source : StackSemStateFiniteExact width C F)
    (_bodyIH : ∀ result post, evaluate (body,source) = (result,post) → post.clock ≤ source.clock)
    (reentryIH : ∀ firstResult middle,
      fixClock source (evaluate (body,source)) = (firstResult,middle) →
      contLoop firstResult = true → middle.clock ≠ 0 →
      ∀ result post, evaluate (.loop body, decClock middle) = (result,post) → post.clock ≤ (decClock middle).clock)
    (result : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F)
    (execution : evaluate (.loop body,source) = (result,post)) : post.clock ≤ source.clock := by
  rw [evaluate_loop] at execution
  rcases bodyRun : fixClock source (evaluate (body,source)) with ⟨firstResult,middle⟩
  have bound := fixClockImp source (evaluate (body,source)) firstResult middle bodyRun
  rw [bodyRun] at execution
  dsimp only at execution
  by_cases continues : contLoop firstResult = true
  · rw [if_pos continues] at execution
    by_cases empty : middle.clock = 0
    · rw [if_pos empty] at execution
      have same := (Prod.mk.inj execution).2
      subst post
      exact bound
    · rw [if_neg empty] at execution
      have next := reentryIH firstResult middle bodyRun continues empty result post execution
      simp only [decClock] at next
      omega
  · rw [if_neg continues] at execution
    have same := (Prod.mk.inj execution).2
    subst post
    exact bound
end Flapjack.StackSemClockControl
