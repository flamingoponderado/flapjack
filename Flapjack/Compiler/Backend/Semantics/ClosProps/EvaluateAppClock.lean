module

public import Flapjack.Compiler.Backend.Semantics.ClosProps.DestClosure
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClock
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength
public import Flapjack.HolRef

@[expose] public section

/-! Clock bounds of the closure application step. -/
namespace Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL

namespace EvaluateAppClockPort
/-- Canonical closure-state finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end EvaluateAppClockPort

/-- An exhausted clock cannot produce a value from a nonempty argument list. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_app_clock0"
  (fmap_as_finite_support := [refs, code])]
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
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_app_clock0_timeout"
  (fmap_as_finite_support := [refs, code])]
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

/-- A successful nonempty application strictly consumes clock time. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_app_clock_less"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateApp_clock_less {C F : Type} (loc_opt : Option Nat) (f : ClosSem.Value)
    (args : List ClosSem.Value) (s1 : ClosSem.State C F) (vs : List ClosSem.Value)
    (s2 : ClosSem.State C F)
    (h : args ≠ [] ∧ ClosSem.evaluateApp loc_opt f args s1 = (.val vs, s2)) :
    s2.clock < s1.clock := by
  obtain ⟨hne, run⟩ := h
  cases args with
  | nil => exact absurd rfl hne
  | cons a rest =>
    simp only [ClosSem.evaluateApp] at run
    split at run
    · simp at run
    · rename_i value found
      split at run
      · simp at run
      · have hs2 : s2 = ClosSem.decClock (a :: rest).length s1 := by
          simp only [Prod.mk.injEq] at run
          exact run.2.symm
        rw [hs2]
        have hpos : 0 < (a :: rest).length := by simp
        simp only [ClosSem.decClock]
        omega
    · rename_i body env rest' found
      split at run
      · simp at run
      · have hcost : 0 < (a :: rest).length - rest'.length := by
          have := ClosSem.destClosure_full_remaining_lt s1.maxApp loc_opt f (a :: rest) env
            rest' body found
          simp only [List.length_cons] at this ⊢
          omega
        cases hnext : ClosSem.fixClock (ClosSem.decClock ((a :: rest).length - rest'.length) s1)
            (ClosSem.evaluate [body] env
              (ClosSem.decClock ((a :: rest).length - rest'.length) s1)) with
        | mk res last =>
          simp only [hnext] at run
          have hlast : last.clock ≤
              (ClosSem.decClock ((a :: rest).length - rest'.length) s1).clock := by
            have hfix := ClosSem.fixClock_clock_le
              (ClosSem.decClock ((a :: rest).length - rest'.length) s1)
              (ClosSem.evaluate [body] env
                (ClosSem.decClock ((a :: rest).length - rest'.length) s1))
            simpa only [hnext] using hfix
          have hstart : (ClosSem.decClock ((a :: rest).length - rest'.length) s1).clock <
              s1.clock := by
            simp only [ClosSem.decClock]
            omega
          split at run
          · rename_i value
            have hs2 : s2 = (ClosSem.evaluateApp loc_opt value rest' last).2 := by
              rw [run]
            rw [hs2]
            have := ClosSem.evaluateApp_clock_le loc_opt value rest' last
            omega
          · simp only [Prod.mk.injEq] at run
            obtain ⟨_, hs2⟩ := run
            rw [← hs2]
            omega

/-- A successful application also drops at least one clock tick per argument. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_app_clock_drop"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateApp_clock_drop {C F : Type} (args : List ClosSem.Value) (f : ClosSem.Value)
    (lopt : Option Nat) (s0 : ClosSem.State C F) (s : ClosSem.State C F)
    (vs : List ClosSem.Value)
    (run : ClosSem.evaluateApp lopt f args s0 = (.val vs, s)) :
    s.clock + args.length ≤ s0.clock := by
  have aux : ∀ n : Nat, ∀ (args : List ClosSem.Value) (f : ClosSem.Value)
      (lopt : Option Nat) (s0 : ClosSem.State C F) (s : ClosSem.State C F)
      (vs : List ClosSem.Value), args.length = n →
      ClosSem.evaluateApp lopt f args s0 = (.val vs, s) → s.clock + args.length ≤ s0.clock := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro args f lopt s0 s vs hlen run
      cases args with
      | nil =>
        simp only [ClosSem.evaluateApp] at run
        simp only [Prod.mk.injEq] at run
        obtain ⟨_, hs⟩ := run
        rw [← hs]
        simp
      | cons a rest =>
        simp only [ClosSem.evaluateApp] at run
        split at run
        · simp at run
        · rename_i value found
          split at run
          · simp at run
          · rename_i hge
            simp only [Prod.mk.injEq] at run
            obtain ⟨_, hs⟩ := run
            rw [← hs]
            simp only [ClosSem.decClock, List.length_cons] at hge ⊢
            omega
        · rename_i body env rest' found
          split at run
          · simp at run
          · rename_i hge
            have hcostLt : rest'.length < (a :: rest).length :=
              ClosSem.destClosure_full_remaining_lt _ _ _ _ _ _ _ found
            have hsum : ((a :: rest).length - rest'.length) + rest'.length =
                (a :: rest).length := Nat.sub_add_cancel hcostLt.le
            cases heval : ClosSem.evaluate [body] env
                (ClosSem.decClock ((a :: rest).length - rest'.length) s0) with
            | mk r' st' =>
              rw [heval] at run
              simp only [ClosSem.fixClock] at run
              have hlast : (min (ClosSem.decClock
                    ((a :: rest).length - rest'.length) s0).clock st'.clock) ≤
                  (ClosSem.decClock ((a :: rest).length - rest'.length) s0).clock :=
                Nat.min_le_left _ _
              cases r' with
              | val values =>
                cases values with
                | nil =>
                  have one := ClosSem.evaluate_length.1 [body] env _ st' []
                    (by rw [heval])
                  simp at one
                | cons v tail =>
                  cases tail with
                  | nil =>
                    have hih := ih rest'.length (by omega) rest' v lopt
                      { st' with clock := min (ClosSem.decClock
                          ((a :: rest).length - rest'.length) s0).clock st'.clock } s vs rfl run
                    simp only [ClosSem.decClock, List.length_cons] at hih hlast hsum hge ⊢
                    omega
                  | cons w more =>
                    have one := ClosSem.evaluate_length.1 [body] env _ st' (v :: w :: more)
                      (by rw [heval])
                    simp at one
              | err error =>
                simp at run
  exact aux args.length args f lopt s0 s vs rfl run

/-- One unfolding step of a nonempty application. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_app_rw"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateApp_rw {C F : Type} (args : List ClosSem.Value) (loc_opt : Option Nat)
    (f : ClosSem.Value) (state : ClosSem.State C F) (h : args ≠ []) :
    ClosSem.evaluateApp loc_opt f args state =
      match ClosSem.destClosure state.maxApp loc_opt f args with
      | none => (.err (.abort .typeError), state)
      | some (.partialApp v) =>
        if state.clock < args.length then (.err (.abort .timeoutError), { state with clock := 0 })
        else (.val [v], ClosSem.decClock args.length state)
      | some (.fullApp exp env restArgs) =>
        if state.clock < args.length - restArgs.length then
          (.err (.abort .timeoutError), { state with clock := 0 })
        else
          match ClosSem.evaluate [exp] env
              (ClosSem.decClock (args.length - restArgs.length) state) with
          | (.val [v], s1) => ClosSem.evaluateApp loc_opt v restArgs s1
          | res => res := by
  cases args with
  | nil => exact absurd rfl h
  | cons a rest =>
    simp only [ClosSem.evaluateApp]
    split
    · rename_i heq
      simp only [heq, ClosSem.typeError]
    · rename_i v heq
      split
      · simp only [heq, ClosSem.timeoutError]
      · simp only [heq]
    · rename_i exp env restArgs heq
      split
      · rename_i hclock
        simp only [heq, ClosSem.timeoutError]
        rw [if_pos hclock]
      · rename_i hclock
        simp only [heq]
        rw [if_neg hclock]
        rw [ClosSem.fixClock_evaluate]
        cases he : ClosSem.evaluate [exp] env
            (ClosSem.decClock ((a :: rest).length - restArgs.length) state) with
        | mk r' st' =>
          cases r' with
          | val values =>
            cases values with
            | nil => rfl
            | cons v tail =>
              cases tail with
              | nil => rfl
              | cons w more => rfl
          | err error => rfl

end Flapjack.Compiler.Backend.ClosProps
