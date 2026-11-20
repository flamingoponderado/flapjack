module

public import Flapjack.Compiler.Backend.Semantics.ClosProps.DestClosure
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
public import Flapjack.HolRef

@[expose] public section

/-! Clock bounds of the closure application step. -/
namespace Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL

/-- An exhausted clock cannot produce a value from a nonempty argument list. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_app_clock0"]
theorem evaluateApp_clock0 {C F : Type} (s0 : ClosSem.State C F)
    (args : List ClosSem.Value) (lopt : Option Nat) (r : ClosSem.Value)
    (vs : List ClosSem.Value) (s : ClosSem.State C F)
    (h : s0.clock = 0 ∧ args ≠ []) :
    ClosSem.evaluateApp lopt r args s0 ≠ (.val vs, s) := by
  obtain ⟨hclock, hne⟩ := h
  cases args with
  | nil => exact absurd rfl hne
  | cons a rest =>
    simp only [ClosSem.evaluateApp]
    split
    · simp [ClosSem.typeError]
    · rename_i value found
      split
      · simp [ClosSem.timeoutError]
      · exfalso
        simp only [List.length_cons] at *
        omega
    · rename_i body env rest' found
      split
      · simp [ClosSem.timeoutError]
      · exfalso
        have hlt := ClosSem.destClosure_full_remaining_lt s0.maxApp lopt r (a :: rest) env
          rest' body found
        omega

/-- With an exhausted clock a nonempty application only aborts on the timeout
or on a type error. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_app_clock0_timeout"]
theorem evaluateApp_clock0_timeout {C F : Type} (s0 : ClosSem.State C F)
    (args : List ClosSem.Value) (lopt : Option Nat) (r : ClosSem.Value)
    (e : ErrorResult ClosSem.Value) (s : ClosSem.State C F)
    (h : s0.clock = 0 ∧ args ≠ [] ∧
      ClosSem.evaluateApp lopt r args s0 = (.err e, s) ∧ e ≠ .abort .typeError) :
    e = .abort .timeoutError := by
  obtain ⟨hclock, hne, run, hneType⟩ := h
  cases args with
  | nil => exact absurd rfl hne
  | cons a rest =>
    simp only [ClosSem.evaluateApp] at run
    split at run
    · rename_i foundNone
      simp only [ClosSem.typeError, Result.err.injEq, Prod.mk.injEq] at run
      exact absurd run.1.symm hneType
    · rename_i value found
      split at run
      · simp only [ClosSem.timeoutError, Result.err.injEq, Prod.mk.injEq] at run
        exact run.1.symm
      · simp at run
    · rename_i body env rest' found
      split at run
      · simp only [ClosSem.timeoutError, Result.err.injEq, Prod.mk.injEq] at run
        exact run.1.symm
      · exfalso
        have hlt := ClosSem.destClosure_full_remaining_lt s0.maxApp lopt r (a :: rest) env
          rest' body found
        omega

end Flapjack.Compiler.Backend.ClosProps
