import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ValueGrowth
import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateCodeFull
import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateClockShift

/-! Consequences of the closure-to-BVL expression simulation postcondition. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- A related target result cannot time out unless the source result did. -/
theorem resultRel_notTimeout {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {source : Result (List ClosSem.Value) ClosSem.Value}
    {target : Result (List BvlSem.Value) BvlSem.Value}
    (related : resultRel (List.Forall₂ (vRel maxApp f refs code)) (vRel maxApp f refs code) source target)
    (notTimeout : source ≠ .err (.abort .timeoutError)) : target ≠ .err (.abort .timeoutError) := by
  intro timeout
  subst target
  cases source with
  | val values => simp [resultRel] at related
  | err error =>
      cases error with
      | raise value => simp [resultRel, excRel] at related
      | abort reason =>
          simp [resultRel, excRel] at related
          subst reason
          exact notTimeout rfl

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

/-- The target witness from a non-timeout source result can run with any
additional clock, preserving its result and extending the final clock. -/
theorem evaluatePost_addClock {C F : Type} (s sNext : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (result : Result (List ClosSem.Value) ClosSem.Value)
    (compiled : List Bvl.Exp) (post : evaluatePost s sNext t targetEnv f result compiled)
    (notTimeout : result ≠ .err (.abort .timeoutError)) (extra : Nat) :
    ∃ (clock : Nat) (targetResult : Result (List BvlSem.Value) BvlSem.Value)
      (tNext : BvlSem.State C F) (fNext : HolFiniteMapExact Nat Nat),
      BvlSem.evaluate compiled targetEnv { t with clock := s.clock + clock + extra } =
        (targetResult, { tNext with clock := tNext.clock + extra }) ∧
      resultRel (List.Forall₂ (vRel s.maxApp fNext tNext.refs tNext.code))
        (vRel s.maxApp fNext tNext.refs tNext.code) result targetResult ∧
      stateRel fNext sNext tNext ∧ relocationSubmap f fNext ∧
      unmappedRefsSubmap t.refs tNext.refs f fNext ∧ codeAnnotations sNext ∧
      sNext.clock = tNext.clock ∧
      stateRel fNext sNext { tNext with clock := tNext.clock + extra } ∧
      sNext.clock + extra = ({ tNext with clock := tNext.clock + extra } : BvlSem.State C F).clock := by
  obtain ⟨clock, targetResult, tNext, fNext, run, results, states, submap, frame, annotations, clocks⟩ := post
  have targetNotTimeout := resultRel_notTimeout results notTimeout
  have shifted := BvlProps.evaluate_addClock compiled targetEnv { t with clock := s.clock + clock }
    tNext targetResult extra run targetNotTimeout
  exact ⟨clock, targetResult, tNext, fNext, shifted, results, states, submap, frame, annotations, clocks,
    (stateRel_clock fNext sNext tNext (tNext.clock + extra)).1.mpr states, by simp [clocks]⟩

end Flapjack.Compiler.Backend.ClosToBvl
