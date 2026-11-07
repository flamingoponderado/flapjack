import Flapjack.HolRef
import Flapjack.Compiler.Backend.SourceEval.Proofs.StateRelation
import Flapjack.EvaluateHOL
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL

/-- Related recording states have equal clocks and remain related after decrement. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "s_rel_clock"]
theorem stateRel_clock {Config F : Type} (ci : CompilerInstance Config) (s t : State F)
    (related : stateRel ci s t) : s.clock = t.clock ∧ stateRel ci (decClock s) (decClock t) := by
  obtain ⟨dec, oracle, refs, target, stores, source, callback, rest⟩ := related
  subst t
  refine ⟨rfl, dec, oracle, refs, ?_, stores, source, callback, rest⟩
  rfl


private theorem concreteRelatedLists (xs ys : List Value)
    (related : List.Forall₂ (fun x y => concreteValue x = true → y = x) xs ys)
    (concrete : concreteValues xs = true) : ys = xs := by
  induction related with
  | nil => rfl
  | cons head tail ih =>
    simp only [concreteValues, Bool.and_eq_true] at concrete
    simp only [head concrete.1, ih concrete.2]

/-- A concrete source value can only be related to itself. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "concrete_v_rel"]
theorem concreteValue_rel (es : EvalOracleState) :
    ∀ x y, ValueRel es x y → concreteValue x = true → y = x := by
  apply valueRel_hol_induction es (fun x y => concreteValue x = true → y = x)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro env id encoded env1 _ concrete
    simp [concreteValue] at concrete
  · intro xs ys related concrete
    have equal := concreteRelatedLists xs ys related (by simpa [concreteValue] using concrete)
    simp [equal]
  · intro stamp xs ys related concrete
    have equal := concreteRelatedLists xs ys related (by simpa [concreteValue] using concrete)
    simp [equal]
  · intro env env1 name body _ concrete
    simp [concreteValue] at concrete
  · intro env env1 funs name _ concrete
    simp [concreteValue] at concrete
  · intro lit _; rfl
  · intro flag index _; rfl
end Flapjack.Compiler.Backend.SourceEval.Proofs
