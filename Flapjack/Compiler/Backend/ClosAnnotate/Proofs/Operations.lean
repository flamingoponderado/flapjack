module

public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.Safety
public import Flapjack.Compiler.Backend.FlatToClos.Proofs.ErrorPropagation

@[expose] public section

/-! Ordinary primitive-operation cases of closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Primitive results relate returned values and states, or relate errors. -/
def AppResultRel {C F : Type} : Result (Value × State C F) Value → Result (Value × State C F) Value → Prop
  | .val (value, state), .val (nextValue, nextState) => ValueRel value nextValue ∧ StateRel state nextState
  | .err error, .err nextError => ResultRel (.err error) (.err nextError)
  | _, _ => False

/-- A primitive simulation obligation, separated from evaluator control flow.
This is Flapjack infrastructure; it does not claim the HOL primitive theorem. -/
def PrimitiveSimulation {C F : Type} (op : ClosLang.Op) : Prop :=
  ∀ (values nextValues : List Value) (source target : State C F),
    List.Forall₂ ValueRel values nextValues → StateRel source target →
    ∃ outcome, doApp op nextValues target = outcome ∧ AppResultRel (doApp op values source) outcome

end Flapjack.Compiler.Backend.ClosAnnotate
