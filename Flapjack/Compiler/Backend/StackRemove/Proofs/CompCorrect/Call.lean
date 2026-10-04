import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.CallTail
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.CallReturnNone
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.CallReturnHandler

namespace Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallAssembly
open Flapjack StackSemEvaluate StackSemStateOps Compiler.Backend.StackLang

/-- Actual imported canonical state codec, without a duplicate carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full Call constructor assembly across every return and handler AST option.
The three match-indexed induction hypotheses are precisely the actual source
branches already checked in the component cases: successful lookup/nonzero
callee entry, successful matching return continuation, and successful matching
exception handler. They retain the fixed original source state and all original
simulation quantifiers. No target execution or post-state fact is assumed.
The native evaluator closure inherits reals_as_rational_cuts (SOUNDNESS item 8),
including arbitrary callee programs; no evaluator-carrier independence is claimed. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectCall {width : Nat} [NeZero width] {C F : Type}
    (ret : Option (HolProg width × Nat × Nat × Nat)) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (calleeIH : match ret with
      | none =>
          ∀ (program : HolProg width),
            StackSemControl.findCode dest source.regs source.code = some program →
            handler = none → source.clock ≠ 0 →
            ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
              (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
            evaluate (program, decClock source) = (r, post) ∧ r ≠ some .error ∧
              stateRelHOL j off k (decClock source) t ∧ StackProps.regBound program k →
            ∃ clock postTarget,
              evaluate (comp j off k program, {t with clock := clock + t.clock}) = (r, postTarget) ∧
              (match r with
               | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
               | _ => stateRelHOL j off k post postTarget)
      | some (_body, link, l1, l2) =>
          ∀ (program : HolProg width),
            StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program →
            source.clock ≠ 0 →
            ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
              (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
            evaluate (program, decClock (setVar link (.loc l1 l2) source)) = (r, post) ∧ r ≠ some .error ∧
              stateRelHOL j off k (decClock (setVar link (.loc l1 l2) source)) t ∧ StackProps.regBound program k →
            ∃ clock postTarget,
              evaluate (comp j off k program, {t with clock := clock + t.clock}) = (r, postTarget) ∧
              (match r with
               | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
               | _ => stateRelHOL j off k post postTarget))
    (returnIH : match ret with
      | none => True
      | some (body, link, l1, l2) =>
          ∀ (program : HolProg width) (middle : StackSemStateFiniteExact width C F),
            StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program →
            source.clock ≠ 0 →
            evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
              (some (.result (.loc l1 l2)), middle) →
            ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
              (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
            evaluate (body, middle) = (r, post) ∧ r ≠ some .error ∧
              stateRelHOL j off k (middle) t ∧ StackProps.regBound body k →
            ∃ clock postTarget,
              evaluate (comp j off k body, {t with clock := clock + t.clock}) = (r, postTarget) ∧
              (match r with
               | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
               | _ => stateRelHOL j off k post postTarget))
    (handlerIH : match ret, handler with
      | some (_body, link, l1, l2), some (handler, hl1, hl2) =>
          ∀ (program : HolProg width) (middle : StackSemStateFiniteExact width C F),
            StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program →
            source.clock ≠ 0 →
            evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
              (some (.exception (.loc hl1 hl2)), middle) →
            ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
              (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
            evaluate (handler, middle) = (r, post) ∧ r ≠ some .error ∧
              stateRelHOL j off k (middle) t ∧ StackProps.regBound handler k →
            ∃ clock postTarget,
              evaluate (comp j off k handler, {t with clock := clock + t.clock}) = (r, postTarget) ∧
              (match r with
               | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
               | _ => stateRelHOL j off k post postTarget)
      | _, _ => True)
    (hypothesis : evaluate (.call ret dest handler, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.call ret dest handler : HolProg width) pointer) :
    ∃ clock postTarget,
      evaluate (comp jump bounds pointer (.call ret dest handler),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  cases ret with
  | none =>
    obtain ⟨clock, postTarget, run, relation⟩ :=
      CallTail.compCorrectCallTail dest handler source result postSource target
        pointer bounds jump calleeIH hypothesis
    refine ⟨clock, postTarget, run, ?_⟩
    cases result with
    | none => exact relation
    | some value => cases value <;> exact relation
  | some returning =>
    rcases returning with ⟨body, link, l1, l2⟩
    cases handler with
    | none =>
      obtain ⟨clock, postTarget, run, relation⟩ :=
        CallReturnNone.compCorrectCallReturnNone body link l1 l2 dest source result
          postSource target pointer bounds jump calleeIH returnIH hypothesis
      refine ⟨clock, postTarget, run, ?_⟩
      cases result with
      | none => exact relation
      | some value => cases value <;> exact relation
    | some exceptional =>
      rcases exceptional with ⟨handlerBody, hl1, hl2⟩
      obtain ⟨clock, postTarget, run, relation⟩ :=
        CallReturnHandler.compCorrectCallReturnHandler body handlerBody link l1 l2 hl1 hl2
          dest source result postSource target pointer bounds jump calleeIH returnIH handlerIH hypothesis
      refine ⟨clock, postTarget, run, ?_⟩
      cases result with
      | none => exact relation
      | some value => cases value <;> exact relation

end Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallAssembly
