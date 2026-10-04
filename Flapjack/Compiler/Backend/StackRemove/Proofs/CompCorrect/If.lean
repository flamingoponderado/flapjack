import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Control
namespace Flapjack.Compiler.Backend.StackRemove.CompCorrect.If
open Flapjack Compiler.Backend.StackLang Compiler.Encoders.Asm StackSemEvaluate StackSemStateOps
/-- Canonical owning-state roundtrip; Flapjack representation infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Source-local operand preservation infrastructure; no independent HOL declaration. -/
theorem operandLookup {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F) (operand : HolRegImm width)
    (relation : stateRelHOL jump bounds pointer source target)
    (lower : match operand with | .reg n => n < pointer | .imm _ => True) :
    StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source =
      StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) target := by
  cases operand with
  | reg n => exact RelationLaws.stateRelGetVar jump bounds pointer n source target ⟨relation, lower⟩
  | imm w => rfl

/-- Genuine original If induction case: original four premises and complete
existential target/result relation, augmented only by the original actual
lookup/comparison-guarded branch induction hypotheses. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectIf {width : Nat} [NeZero width] {C F : Type}
    (comparison : Cmp) (register : Nat) (operand : HolRegImm width)
    (first second : HolProg width)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (firstIH : ∀ (left right : WordLocW width),
      getVar register source = some left →
      StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some right →
      wordSemWordCmp comparison left right = some true →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (first, source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k source t ∧ StackProps.regBound first k →
      ∃ clock postTarget,
        evaluate (comp j off k first, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (secondIH : ∀ (left right : WordLocW width),
      getVar register source = some left →
      StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some right →
      wordSemWordCmp comparison left right = some false →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (second, source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k source t ∧ StackProps.regBound second k →
      ∃ clock postTarget,
        evaluate (comp j off k second, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (hypothesis : evaluate (.ite comparison register operand first second, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.ite comparison register operand first second) pointer) :
    ∃ clock postTarget,
      evaluate (comp jump bounds pointer (.ite comparison register operand first second),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  simp only [StackProps.regBound] at lower
  have leftEq := RelationLaws.stateRelGetVar jump bounds pointer register source target ⟨relation, lower.1⟩
  have rightEq := operandLookup jump bounds pointer source target operand relation lower.2.1
  rw [evaluate_ite] at sourceRun
  cases leftLookup : getVar register source with
  | none =>
    rw [leftLookup] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some left =>
    rw [leftLookup] at sourceRun
    cases rightLookup : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source with
    | none =>
      rw [rightLookup] at sourceRun
      exact (notError (Prod.mk.inj sourceRun).1.symm).elim
    | some right =>
      rw [rightLookup] at sourceRun
      simp only [] at sourceRun
      cases compared : wordSemWordCmp comparison left right with
      | none =>
        rw [compared] at sourceRun
        exact (notError (Prod.mk.inj sourceRun).1.symm).elim
      | some truth =>
        cases truth with
        | false =>
          rw [compared] at sourceRun
          obtain ⟨clock, postTarget, targetRun, postRelation⟩ :=
            secondIH left right leftLookup rightLookup compared result postSource target pointer bounds jump
              ⟨sourceRun, notError, relation, lower.2.2.2⟩
          have targetLeft : getVar register {target with clock := clock + target.clock} = some left :=
            leftEq.symm.trans leftLookup
          have targetRight : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand)
              {target with clock := clock + target.clock} = some right := by
            have same : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand)
                {target with clock := clock + target.clock} =
                StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) target := by
              cases operand <;> rfl
            exact same.trans (rightEq.symm.trans rightLookup)
          refine ⟨clock, postTarget, ?_, ?_⟩
          · rw [comp, evaluate_ite, targetLeft, targetRight]
            simpa only [compared] using targetRun
          · cases result with
            | none => exact postRelation
            | some value => cases value <;> exact postRelation
        | true =>
          rw [compared] at sourceRun
          obtain ⟨clock, postTarget, targetRun, postRelation⟩ :=
            firstIH left right leftLookup rightLookup compared result postSource target pointer bounds jump
              ⟨sourceRun, notError, relation, lower.2.2.1⟩
          have targetLeft : getVar register {target with clock := clock + target.clock} = some left :=
            leftEq.symm.trans leftLookup
          have targetRight : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand)
              {target with clock := clock + target.clock} = some right := by
            have same : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand)
                {target with clock := clock + target.clock} =
                StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) target := by
              cases operand <;> rfl
            exact same.trans (rightEq.symm.trans rightLookup)
          refine ⟨clock, postTarget, ?_, ?_⟩
          · rw [comp, evaluate_ite, targetLeft, targetRight]
            simpa only [compared] using targetRun
          · cases result with
            | none => exact postRelation
            | some value => cases value <;> exact postRelation
end Flapjack.Compiler.Backend.StackRemove.CompCorrect.If
