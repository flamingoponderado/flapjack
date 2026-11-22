module

public import Flapjack.Compiler.Backend.Semantics.ClosProps.DestClosure
public import Flapjack.Compiler.Backend.Semantics.ClosProps.EvaluateConst
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

/-- Composing clock subtractions. -/
private theorem decClock_decClock {C F : Type} (first second : Nat) (state : ClosSem.State C F) :
    ClosSem.decClock first (ClosSem.decClock second state) =
      ClosSem.decClock (first + second) state := by
  simp only [ClosSem.decClock]
  congr 1
  omega

/-- A successful application returns a singleton value list. -/
private theorem evaluateApp_singleton {C F : Type} (location : Option Nat)
    (function : ClosSem.Value) (args : List ClosSem.Value) (state next : ClosSem.State C F)
    (values : List ClosSem.Value)
    (run : ClosSem.evaluateApp location function args state = (.val values, next)) :
    values = [@Flapjack.holHd ClosSem.Value ⟨ClosSem.unitValue⟩ values] := by
  have len := ClosSem.evaluate_length.2 location function args state next values run
  cases values with
  | nil => simp at len
  | cons value tail =>
    cases tail with
    | nil => rfl
    | cons other more => simp at len

/-- Applying no further arguments after a successful application is the
identity. -/
private theorem evaluateApp_nil_append {C F : Type} (function : ClosSem.Value)
    (args : List ClosSem.Value) (state : ClosSem.State C F) :
    ClosSem.evaluateApp none function args state =
      match ClosSem.evaluateApp none function args state with
      | (.val vs1, s1) =>
        ClosSem.evaluateApp none
          (@Flapjack.holHd ClosSem.Value ⟨ClosSem.unitValue⟩ vs1) [] s1
      | (.err v7, s1) => (.err v7, s1) := by
  cases run : ClosSem.evaluateApp none function args state with
  | mk r next =>
    cases r with
    | err error => rfl
    | val values =>
      have singleton := evaluateApp_singleton none function args state next values run
      rw [singleton]
      simp only [ClosSem.evaluateApp]
      rfl

/-- Appending arguments to a successful application matches applying the whole
list at once. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_app_append"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateApp_append {C F : Type} (args2 : List ClosSem.Value) (f : ClosSem.Value)
    (args1 : List ClosSem.Value) (state : ClosSem.State C F)
    (h : (args1 ++ args2).length ≤ state.maxApp) :
    ClosSem.evaluateApp none f (args1 ++ args2) state =
      match ClosSem.evaluateApp none f args2 state with
      | (.val vs1, s1) =>
        ClosSem.evaluateApp none
          (@Flapjack.holHd ClosSem.Value ⟨ClosSem.unitValue⟩ vs1) args1 s1
      | (.err v7, s1) => (.err v7, s1) := by
  have aux : ∀ n : Nat, ∀ (args2 : List ClosSem.Value) (f : ClosSem.Value)
      (args1 : List ClosSem.Value) (state : ClosSem.State C F),
      args2.length = n → (args1 ++ args2).length ≤ state.maxApp →
      ClosSem.evaluateApp none f (args1 ++ args2) state =
        match ClosSem.evaluateApp none f args2 state with
        | (.val vs1, s1) =>
          ClosSem.evaluateApp none
            (@Flapjack.holHd ClosSem.Value ⟨ClosSem.unitValue⟩ vs1) args1 s1
        | (.err v7, s1) => (.err v7, s1) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro args2 f args1 state hlen bound
      cases args1 with
      | nil => exact evaluateApp_nil_append f args2 state
      | cons a args1' =>
        cases args2 with
        | nil =>
          simp only [List.append_nil]
          have emptyRun : ClosSem.evaluateApp none f [] state =
              (.val [f], state) := by
            simp only [ClosSem.evaluateApp]
          rw [emptyRun]
          simp only [Flapjack.holHd]
        | cons b args2' =>
          have bound' : (a :: args1').length + (b :: args2').length ≤ state.maxApp := by
            rw [List.length_append] at bound
            exact bound
          have lengths : ((a :: args1') ++ (b :: args2')).length =
              (a :: args1').length + (b :: args2').length := List.length_append
          have hne1 : (a :: args1') ++ (b :: args2') ≠ [] := by simp
          have hne2 : b :: args2' ≠ [] := by simp
          have hne3 : a :: args1' ≠ [] := by simp
          rw [evaluateApp_rw ((a :: args1') ++ (b :: args2')) none f state hne1]
          rw [evaluateApp_rw (b :: args2') none f state hne2]
          cases hD : ClosSem.destClosure state.maxApp none f (b :: args2') with
          | none =>
            have hD' := destClosure_none_append (α := Unit) state.maxApp () f
              (a :: args1') (b :: args2') hD
            simp only [hD']
          | some kind =>
            cases kind with
            | partialApp cl =>
              simp only []
              split
              · rename_i hD1
                have hnone := destClosure_none_append2 (α := Unit) state.maxApp () f
                  (a :: args1') (b :: args2') ⟨bound', hD1⟩
                rw [hnone] at hD
                simp at hD
              · rename_i v hD1
                have htwice := destClosure_partial_twice state.maxApp f (a :: args1')
                  (b :: args2') cl (some (.partialApp v)) ⟨bound', hD1, hD⟩
                by_cases hclock2 : state.clock < (b :: args2').length
                · rw [if_pos hclock2]
                  simp only []
                  rw [if_pos (by omega)]
                · rw [if_neg hclock2]
                  simp only []
                  simp only [Flapjack.holHd]
                  rw [evaluateApp_rw (a :: args1') none cl
                    (ClosSem.decClock (b :: args2').length state) hne3]
                  have hmax : (ClosSem.decClock (b :: args2').length state).maxApp =
                      state.maxApp := by
                    simp only [ClosSem.decClock]
                  simp only [hmax, htwice]
                  by_cases hclock1 : (ClosSem.decClock (b :: args2').length state).clock <
                      (a :: args1').length
                  · rw [if_pos hclock1]
                    rw [if_pos (by
                      simp only [ClosSem.decClock] at hclock1
                      simp only [lengths]
                      omega)]
                    rfl
                  · rw [if_neg hclock1]
                    rw [if_neg (by
                      simp only [ClosSem.decClock] at hclock1
                      simp only [lengths]
                      omega)]
                    rw [lengths, decClock_decClock]
              · rename_i e env rest hD1
                have htwice := destClosure_partial_twice state.maxApp f (a :: args1')
                  (b :: args2') cl (some (.fullApp e env rest)) ⟨bound', hD1, hD⟩
                have hrest := destClosure_rest_length state.maxApp cl (a :: args1') e env
                  rest htwice
                by_cases hclock2 : state.clock < (b :: args2').length
                · rw [if_pos hclock2]
                  simp only []
                  rw [if_pos (by omega)]
                · rw [if_neg hclock2]
                  simp only []
                  simp only [Flapjack.holHd]
                  rw [evaluateApp_rw (a :: args1') none cl
                    (ClosSem.decClock (b :: args2').length state) hne3]
                  have hmax : (ClosSem.decClock (b :: args2').length state).maxApp =
                      state.maxApp := by
                    simp only [ClosSem.decClock]
                  simp only [hmax, htwice]
                  have costEq : ((a :: args1') ++ (b :: args2')).length - rest.length =
                      ((a :: args1').length - rest.length) + (b :: args2').length := by
                    rw [lengths]
                    omega
                  rw [costEq]
                  by_cases hclock1 : (ClosSem.decClock (b :: args2').length state).clock <
                      (a :: args1').length - rest.length
                  · rw [if_pos hclock1]
                    rw [if_pos (by
                      simp only [ClosSem.decClock] at hclock1
                      omega)]
                    rfl
                  · rw [if_neg hclock1]
                    rw [if_neg (by
                      simp only [ClosSem.decClock] at hclock1
                      omega)]
                    rw [decClock_decClock]
            | fullApp body env rest2 =>
              have hadd := destClosure_full_addargs state.maxApp f (b :: args2') body env rest2
                (a :: args1') ⟨hD, bound'⟩
              have hrest := destClosure_rest_length state.maxApp f (b :: args2') body env rest2 hD
              simp only []
              simp only [hadd]
              have costEq : ((a :: args1') ++ (b :: args2')).length -
                  ((a :: args1') ++ rest2).length = (b :: args2').length - rest2.length := by
                rw [lengths, List.length_append]
                omega
              rw [costEq]
              by_cases hclock : state.clock < (b :: args2').length - rest2.length
              · simp only [if_pos hclock]
              · simp only [if_neg hclock]
                cases run : ClosSem.evaluate [body] env
                    (ClosSem.decClock ((b :: args2').length - rest2.length) state) with
                | mk r st =>
                  cases r with
                  | err error => rfl
                  | val values =>
                    cases values with
                    | nil =>
                      exfalso
                      have singleton := ClosSem.evaluate_length.1 [body] env
                        (ClosSem.decClock ((b :: args2').length - rest2.length) state)
                        st [] run
                      simp at singleton
                    | cons value tail =>
                      cases tail with
                      | nil =>
                        have bodyMax := evaluateConst [body] env
                          (ClosSem.decClock ((b :: args2').length - rest2.length) state)
                          (.val [value]) st run
                        have startMax : (ClosSem.decClock
                            ((b :: args2').length - rest2.length) state).maxApp = state.maxApp := by
                          simp only [ClosSem.decClock]
                        have hbound : ((a :: args1') ++ rest2).length ≤ st.maxApp := by
                          rw [bodyMax, startMax, List.length_append]
                          omega
                        exact ih rest2.length (by omega) rest2 value (a :: args1') st rfl hbound
                      | cons other more =>
                        exfalso
                        have singleton := ClosSem.evaluate_length.1 [body] env
                          (ClosSem.decClock ((b :: args2').length - rest2.length) state)
                          st (value :: other :: more) run
                        simp at singleton
  exact aux args2.length args2 f args1 state rfl h

end Flapjack.Compiler.Backend.ClosProps
