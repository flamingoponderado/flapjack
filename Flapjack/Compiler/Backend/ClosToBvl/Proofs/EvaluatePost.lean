module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ValueGrowth
public import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateCodeFull
public import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateClockShift

@[expose] public section

/-! Consequences of the closure-to-BVL expression simulation postcondition. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- A successful simulation witness preserves the environment for the next
expression and supplies the code-growth fact proved by BVL evaluation. This
is untagged composition infrastructure for the candidate pass simulation. -/
theorem evaluatePost_environment {C F : Type} (s sNext : ClosSem.State C F)
    (t : BvlSem.State C F) (env : List ClosSem.Value) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (result : Result (List ClosSem.Value) ClosSem.Value)
    (compiled : List Bvl.Exp)
    (envRelated : envRel s.maxApp f t.refs t.code env targetEnv)
    (post : evaluatePost s sNext t targetEnv f result compiled) :
    ∃ (extraClock : Nat) (targetResult : Result (List BvlSem.Value) BvlSem.Value)
      (tNext : BvlSem.State C F) (fNext : HolFiniteMapExact Nat Nat),
      BvlSem.evaluate compiled targetEnv { t with clock := s.clock + extraClock } = (targetResult, tNext) ∧
      resultRel (List.Forall₂ (vRel s.maxApp fNext tNext.refs tNext.code))
        (vRel s.maxApp fNext tNext.refs tNext.code) result targetResult ∧
      stateRel fNext sNext tNext ∧ relocationSubmap f fNext ∧
      unmappedRefsSubmap t.refs tNext.refs f fNext ∧ codeAnnotations sNext ∧
      sNext.clock = tNext.clock ∧ sptSubspt t.code tNext.code ∧
      envRel s.maxApp fNext tNext.refs tNext.code env targetEnv := by
  obtain ⟨clock, targetResult, tNext, fNext, run, results, states, submap, frame, annotations, clocks⟩ := post
  have growth : sptSubspt t.code tNext.code := by
    exact BvlProps.evaluateMono compiled targetEnv { t with clock := s.clock + clock } targetResult tNext run
  exact ⟨clock, targetResult, tNext, fNext, run, results, states, submap, frame, annotations, clocks,
    growth, envRel_grow envRelated submap frame growth⟩

end Flapjack.Compiler.Backend.ClosToBvl
