module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.AppClockShift

@[expose] public section

/-! Closure-evaluation clock extension. -/
namespace Flapjack.Compiler.Backend.ClosProps.ClockShiftPort
open Flapjack ClosSem SemanticPrimitivesHOL

/-- Closure states use the canonical finite-map codec. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Evaluation and closure application preserve non-timeout results when
the same amount of clock is added to the initial and final states. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_add_to_clock"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_addToClock {C F : Type} (extra : Nat) :
    (∀ (p : List ClosLang.Exp × List ClosSem.Value × State C F)
      (es : List ClosLang.Exp) (env : List ClosSem.Value) (s : State C F)
      (r : Result (List ClosSem.Value) ClosSem.Value) (s1 : State C F),
      p = (es, env, s) ∧ evaluate es env s = (r, s1) ∧ r ≠ .err (.abort .timeoutError) →
      evaluate es env { s with clock := s.clock + extra } = (r, { s1 with clock := s1.clock + extra })) ∧
    (∀ (loc : Option Nat) (v : ClosSem.Value) (args : List ClosSem.Value) (s : State C F)
      (r : Result (List ClosSem.Value) ClosSem.Value) (s1 : State C F),
      evaluateApp loc v args s = (r, s1) ∧ r ≠ .err (.abort .timeoutError) →
      evaluateApp loc v args { s with clock := s.clock + extra } = (r, { s1 with clock := s1.clock + extra })) := by
  constructor
  · intro p es env s r s1 h
    exact evaluate_addClock.1 es env s s1 r extra h.2.1 h.2.2
  · intro loc v args s r s1 h
    exact evaluate_addClock.2 loc v args s s1 r extra h.1 h.2

/-- A non-timeout expression evaluation remains valid with any extra clock. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_add_clock"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_addClock {C F : Type} (s1 s : State C F)
    (r : Result (List ClosSem.Value) ClosSem.Value) (es : List ClosLang.Exp) (env : List ClosSem.Value)
    (h : evaluate es env s = (r, s1) ∧ r ≠ .err (.abort .timeoutError)) :
    ∀ extra, evaluate es env { s with clock := s.clock + extra } = (r, { s1 with clock := s1.clock + extra }) := by
  intro extra
  exact ClosSem.evaluate_addClock.1 es env s s1 r extra h.1 h.2

end Flapjack.Compiler.Backend.ClosProps.ClockShiftPort
