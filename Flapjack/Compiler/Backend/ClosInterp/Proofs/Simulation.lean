import Flapjack.Compiler.Backend.ClosInterp.Proofs.EvaluateBasic

/-! Clock-bounded induction hypothesis used by the interpreter-insertion
correctness proof. The evaluator and state relation are proof-side and await
full cross-language review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL

/-- Evaluations and applications with at most the given clock are simulated
in related interpreter states, possibly with additional target clock. -/
def InterpAssum (C F : Type) (bound : Nat) : Prop :=
  (∀ (expressions : List ClosLang.Exp) (source : ClosSem.State C F)
      (env : List ClosSem.Value) (target : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value) (sourceFinal : ClosSem.State C F),
    source.clock ≤ bound →
    ClosSem.evaluate expressions env source = (result, sourceFinal) →
    result ≠ .err (.abort .typeError) → StateRel source target →
    ∃ extra targetFinal,
      ClosSem.evaluate expressions env { target with clock := extra + target.clock } = (result, targetFinal) ∧
      StateRel sourceFinal targetFinal) ∧
  (∀ (args : List ClosSem.Value) (source : ClosSem.State C F) (location : Option Nat)
      (function : ClosSem.Value) (target : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value) (sourceFinal : ClosSem.State C F),
    source.clock ≤ bound →
    ClosSem.evaluateApp location function args source = (result, sourceFinal) →
    result ≠ .err (.abort .typeError) → StateRel source target →
    ∃ extra targetFinal,
      ClosSem.evaluateApp location function args { target with clock := extra + target.clock } = (result, targetFinal) ∧
      StateRel sourceFinal targetFinal)

/-- A clock-bounded simulation is available at every smaller bound. -/
theorem interpAssum_le {C F : Type} {larger smaller : Nat}
    (assumption : InterpAssum C F larger) (bound : smaller ≤ larger) : InterpAssum C F smaller := by
  constructor
  · intro expressions source env target result sourceFinal clock run notTypeError related
    exact assumption.1 expressions source env target result sourceFinal (Nat.le_trans clock bound) run notTypeError related
  · intro args source location function target result sourceFinal clock run notTypeError related
    exact assumption.2 args source location function target result sourceFinal (Nat.le_trans clock bound) run notTypeError related

end Flapjack.Compiler.Backend.ClosInterp
