import Flapjack.Compiler.Backend.BvlInline.Proofs.InlineForce

/-! The non-inlined Call case of BVL inlining simulation. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BvlProps Flapjack.SemanticPrimitivesHOL

namespace InlineDirectCallCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end InlineDirectCallCarrier

/-- The Call/Call expression-relation case of the inlining simulation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "evaluate_inline"
  (fmap_as_finite_support := [refs])]
theorem evaluateInline_call {C F : Type} (limit ticks : Nat) (dest : Option Nat)
    (args args' : List Bvl.Exp) (env : List BvlSem.Value)
    (source final : Flapjack.Compiler.Backend.BvlSem.State (Spt (Nat × Bvl.Exp) × C) F)
    (target : Flapjack.Compiler.Backend.BvlSem.State C F)
    (argsIH : ∀ (s last : State (Spt (Nat × Bvl.Exp) × C) F) (t : State C F)
      (res : Result (List BvlSem.Value) BvlSem.Value),
      inStateRel limit s t → ExpRel s.code args args' →
      evaluateTuple (args, env, s) = (res, last) → res ≠ .err (.abort .typeError) →
      ∃ targetLast, evaluateTuple (args', env, t) = (res, targetLast) ∧ inStateRel limit last targetLast)
    (bodyIH : ∀ (middle last : State (Spt (Nat × Bvl.Exp) × C) F) (targetMiddle : State C F)
      (values : List BvlSem.Value) (body body' : Bvl.Exp)
      (res : Result (List BvlSem.Value) BvlSem.Value),
      middle.clock ≤ source.clock → ticks + 1 ≤ middle.clock →
      inStateRel limit middle targetMiddle → ExpRel middle.code [body] [body'] →
      evaluateTuple ([body], values, decClock (ticks + 1) middle) = (res, last) →
      res ≠ .err (.abort .typeError) →
      ∃ targetLast, evaluateTuple ([body'], values, decClock (ticks + 1) targetMiddle) = (res, targetLast) ∧
        inStateRel limit last targetLast)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (related : inStateRel limit source target)
    (expressions : ExpRel source.code [.call ticks dest args] [.call ticks dest args'])
    (run : evaluateTuple ([.call ticks dest args], env, source) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetFinal, evaluateTuple ([.call ticks dest args'], env, target) = (result, targetFinal) ∧
      inStateRel limit final targetFinal := by
  cases expressions with
  | call argsRel =>
    simp only [evaluateTuple] at run
    rw [evaluate, fixClock_evaluate] at run
    cases argsRun : evaluate args env source with
    | mk argsResult middle =>
      rw [argsRun] at run
      have bound : middle.clock ≤ source.clock := by
        have h := evaluate_clock_le args env source
        simpa [argsRun] using h
      have argsNotType : argsResult ≠ .err (.abort .typeError) := by
        cases argsResult with
        | val values => simp
        | err error =>
          simp at run
          rcases run with ⟨rfl, _⟩
          exact notTypeError
      obtain ⟨targetMiddle, targetArgs, middleRel⟩ :=
        argsIH source middle target argsResult related argsRel argsRun argsNotType
      change evaluate args' env target = _ at targetArgs
      cases argsResult with
      | err error =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨targetMiddle, by rw [evaluateTuple, evaluate, fixClock_evaluate, targetArgs], middleRel⟩
      | val values =>
        cases found : findCode dest values middle.code with
        | none =>
          simp [found] at run
          exact False.elim (notTypeError run.1.symm)
        | some pair =>
          obtain ⟨callValues, body⟩ := pair
          obtain ⟨body', targetFound, bodyRel⟩ :=
            inStateRel_findCode limit middle targetMiddle middleRel dest values callValues body found
          by_cases timeout : middle.clock < ticks + 1
          · have targetTimeout : targetMiddle.clock < ticks + 1 := by simpa [middleRel.2.2.1] using timeout
            simp [found, timeout] at run
            rcases run with ⟨rfl, rfl⟩
            refine ⟨{ targetMiddle with clock := 0 }, ?_, ?_⟩
            · rw [evaluateTuple, evaluate, fixClock_evaluate, targetArgs]
              simp [targetFound, targetTimeout]
            · simpa [inStateRel] using
                And.intro middleRel.1 (And.intro middleRel.2.1 middleRel.2.2.2)
          · have targetEnough : ¬targetMiddle.clock < ticks + 1 := by simpa [middleRel.2.2.1] using timeout
            have enough : ticks + 1 ≤ middle.clock := Nat.le_of_not_gt timeout
            simp [found, timeout] at run
            obtain ⟨targetFinal, targetBody, finalRel⟩ :=
              bodyIH middle final targetMiddle callValues body body' result bound enough middleRel bodyRel run notTypeError
            refine ⟨targetFinal, ?_, finalRel⟩
            rw [evaluateTuple, evaluate, fixClock_evaluate, targetArgs]
            simpa [targetFound, targetEnough, evaluateTuple] using targetBody

end Flapjack.Compiler.Backend.BvlInline.Proofs
