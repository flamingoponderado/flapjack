import Flapjack.Compiler.Backend.BviInline.Proofs.RemoveTicksRelation
import Flapjack.Compiler.Backend.Semantics.BviProps.EvaluateClockShift

/-! Evaluator cases for BVI tick removal. -/
namespace Flapjack.Compiler.Backend.BviInline.RemoveTicksCases
open BviSem
open BvlSem (Value)

/-- Flapjack infrastructure: cleaned expressions can be simulated by the
original expressions with enough extra clock, preserving related states. -/
def Property {C F : Type} (xs : List Bvi.Exp) (env : List Value) (target : BviState C F) : Prop :=
  ∀ (source : BviState C F) (result : BviResult) (targetNext : BviState C F),
    RemoveStateRel source target → evaluate (removeTicksListSource xs) env target = (result, targetNext) →
    ∃ extra sourceNext, evaluate xs env { source with clock := source.clock + extra } = (result, sourceNext) ∧
      RemoveStateRel sourceNext targetNext

/-- Flapjack infrastructure: the empty expression list needs no extra clock. -/
theorem nil {C F : Type} (env : List Value) (target : BviState C F) : Property [] env target := by
  intro source result targetNext states run
  simp [removeTicksListSource, evaluate] at run
  obtain ⟨rfl, rfl⟩ := run.symm
  exact ⟨0, source, by simp [evaluate], states⟩

/-- Flapjack infrastructure: variable lookup is unaffected by tick removal. -/
theorem var {C F : Type} (index : Nat) (env : List Value) (target : BviState C F) :
    Property [.var index] env target := by
  intro source result targetNext states run
  cases found : env[index]? with
  | none =>
    simp [removeTicksListSource, removeTicksSource, evaluate, found] at run
    obtain ⟨rfl, rfl⟩ := run.symm
    exact ⟨0, source, by simp [evaluate, found], states⟩
  | some value =>
    simp [removeTicksListSource, removeTicksSource, evaluate, found] at run
    obtain ⟨rfl, rfl⟩ := run.symm
    exact ⟨0, source, by simp [evaluate, found], states⟩

/-- Flapjack infrastructure: restoring a removed tick costs exactly one
additional clock unit beyond those required by its body. -/
theorem tick {C F : Type} (body : Bvi.Exp) (env : List Value) (target : BviState C F)
    (bodyIH : Property [body] env target) : Property [.tick body] env target := by
  intro source result targetNext states run
  have bodyRun : evaluate (removeTicksListSource [body]) env target = (result, targetNext) := by
    simpa [removeTicksListSource, removeTicksSource] using run
  obtain ⟨extra, sourceNext, sourceRun, finalRel⟩ := bodyIH source result targetNext states bodyRun
  refine ⟨extra + 1, sourceNext, ?_, finalRel⟩
  have nonzero : source.clock + (extra + 1) ≠ 0 := by omega
  have decremented : BviSem.decClock 1 { source with clock := source.clock + (extra + 1) } =
      { source with clock := source.clock + extra } := by
    simp [BviSem.decClock]
  simpa [evaluate, nonzero, decremented] using sourceRun

/-- Flapjack infrastructure: raising a tick-cleaned body propagates the
simulated body result without consuming additional clock. -/
theorem raiseExp {C F : Type} (body : Bvi.Exp) (env : List Value) (target : BviState C F)
    (bodyIH : Property [body] env target) : Property [.raise body] env target := by
  intro source result targetNext states run
  cases bodyRun : evaluate (removeTicksListSource [body]) env target with
  | mk bodyResult bodyNext =>
    obtain ⟨extra, sourceNext, sourceRun, finalRel⟩ := bodyIH source bodyResult bodyNext states bodyRun
    have bodyRun' : evaluate [removeTicksSource body] env target = (bodyResult, bodyNext) := by
      simpa [removeTicksListSource] using bodyRun
    cases bodyResult with
    | err error =>
      simp [removeTicksListSource, removeTicksSource, evaluate, bodyRun'] at run
      obtain ⟨rfl, rfl⟩ := run.symm
      exact ⟨extra, sourceNext, by simp [evaluate, sourceRun], finalRel⟩
    | val values =>
      simp [removeTicksListSource, removeTicksSource, evaluate, bodyRun'] at run
      obtain ⟨rfl, rfl⟩ := run.symm
      exact ⟨extra, sourceNext, by simp [evaluate, sourceRun], finalRel⟩

/-- Flapjack infrastructure: returned values and errors transfer from a
cleaned argument list to the original return expression. -/
theorem returnExp {C F : Type} (args : List Bvi.Exp) (env : List Value) (target : BviState C F)
    (argsIH : Property args env target) : Property [.return args] env target := by
  intro source result targetNext states run
  cases argsRun : evaluate (removeTicksListSource args) env target with
  | mk argsResult argsNext =>
    obtain ⟨extra, sourceNext, sourceRun, finalRel⟩ := argsIH source argsResult argsNext states argsRun
    cases argsResult with
    | err error =>
      simp [removeTicksListSource, removeTicksSource, evaluate, argsRun] at run
      obtain ⟨rfl, rfl⟩ := run.symm
      exact ⟨extra, sourceNext, by simp [evaluate, sourceRun], finalRel⟩
    | val values =>
      simp [removeTicksListSource, removeTicksSource, evaluate, argsRun] at run
      obtain ⟨rfl, rfl⟩ := run.symm
      exact ⟨extra, sourceNext, by simp [evaluate, sourceRun], finalRel⟩

end Flapjack.Compiler.Backend.BviInline.RemoveTicksCases
