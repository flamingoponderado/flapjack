import Flapjack.EvaluateHOL.ClockFull
import Lean.Elab.Tactic.Omega

/-! Source evaluator result-length infrastructure. Full HOL statement and
carrier review remains open. -/
namespace Flapjack.EvaluateProps
open Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL Flapjack.AstHOL Flapjack.EvaluateHOL

mutual
/-- A successful source expression-list evaluation returns one value per
expression. This is untagged pending full source-evaluator review. -/
theorem evaluateLengthFull {σ : Type} (st next : State σ) (env : SemEnv Value)
    (expressions : List AstHOL.Exp) (values : List Value)
    (run : evaluate st env expressions = (next, .val values)) : values.length = expressions.length := by
  cases expressions with
  | nil => simp [evaluate] at run; simp [← run.2]
  | cons first rest =>
    cases rest with
    | cons second tail =>
      rw [evaluate, (fixClockEvaluate st env [first] []).1] at run
      cases firstRun : evaluate st env [first] with
      | mk middle firstResult =>
        rw [firstRun] at run
        cases firstResult with
        | err error => simp at run
        | val firstValues =>
          cases tailRun : evaluate middle env (second :: tail) with
          | mk final tailResult =>
            rw [tailRun] at run
            cases tailResult with
            | err error => simp at run
            | val tailValues =>
              simp only [Prod.mk.injEq, Result.val.injEq] at run
              have bound := evaluateClockFull st middle env [first] (.val firstValues) firstRun
              have tailLength := evaluateLengthFull middle final env (second :: tail) tailValues tailRun
              simp only [List.length_cons]
              rw [← run.2]
              simpa using congrArg Nat.succ tailLength
    | nil =>
      cases first with
      | lit lit => simp [evaluate] at run; simp [← run.2]
      | var name =>
        rw [evaluate] at run
        split at run <;> simp_all [typeError]
        rw [← run.2]
        rfl
      | fn name body => simp [evaluate] at run; simp [← run.2]
      | raise body =>
        rw [evaluate] at run
        split at run <;> simp_all
      | tannot body typ =>
        rw [evaluate] at run
        exact evaluateLengthFull st next env [body] values run
      | lannot body loc =>
        cases loc
        rw [evaluate] at run
        exact evaluateLengthFull st next env [body] values run
      | con name args =>
        rw [evaluate] at run
        split at run
        · cases argRun : evaluate st env args.reverse with
          | mk middle argResult =>
            rw [argRun] at run
            cases argResult with
            | err error => simp at run
            | val argValues =>
              dsimp only at run
              split at run <;> simp_all [typeError]
              rw [← run.2]
              rfl
        · simp [typeError] at run
      | letrec funs body =>
        rw [evaluate] at run
        split at run
        · exact evaluateLengthFull st next _ [body] values run
        · simp [typeError] at run
      | let_ name first body =>
        rw [evaluate, (fixClockEvaluate st env [first] []).1] at run
        cases firstRun : evaluate st env [first] with
        | mk middle firstResult =>
          rw [firstRun] at run
          cases firstResult with
          | err error => simp at run
          | val firstValues =>
            have bound := evaluateClockFull st middle env [first] (.val firstValues) firstRun
            exact evaluateLengthFull middle next _ [body] values run
      | if_ cond yes no =>
        rw [evaluate, (fixClockEvaluate st env [cond] []).1] at run
        cases condRun : evaluate st env [cond] with
        | mk middle condResult =>
          rw [condRun] at run
          cases condResult with
          | err error => simp at run
          | val condValues =>
            have bound := evaluateClockFull st middle env [cond] (.val condValues) condRun
            dsimp only at run
            cases selected : doIf (headValue condValues) yes no with
            | none => rw [selected] at run; simp [typeError] at run
            | some branch =>
              rw [selected] at run
              rcases doIf_selected (headValue condValues) yes no branch selected with equal | equal
              · subst branch; exact evaluateLengthFull middle next env [yes] values run
              · subst branch; exact evaluateLengthFull middle next env [no] values run
      | log op first second =>
        rw [evaluate, (fixClockEvaluate st env [first] []).1] at run
        cases firstRun : evaluate st env [first] with
        | mk middle firstResult =>
          rw [firstRun] at run
          cases firstResult with
          | err error => simp at run
          | val firstValues =>
            have bound := evaluateClockFull st middle env [first] (.val firstValues) firstRun
            dsimp only at run
            cases selected : doLog op (headValue firstValues) second with
            | none => rw [selected] at run; simp [typeError] at run
            | some outcome =>
              rw [selected] at run
              cases outcome with
              | val value => simp at run; simp [← run.2]
              | exp body =>
                have same := doLog_selected op (headValue firstValues) second body selected
                subst body
                exact evaluateLengthFull middle next env [second] values run
      | mat body rows =>
        rw [evaluate, (fixClockEvaluate st env [body] []).1] at run
        cases bodyRun : evaluate st env [body] with
        | mk middle bodyResult =>
          rw [bodyRun] at run
          cases bodyResult with
          | err error => simp at run
          | val bodyValues =>
            have bound := evaluateClockFull st middle env [body] (.val bodyValues) bodyRun
            dsimp only at run
            split at run
            · exact evaluateMatchLengthFull middle next env _ rows bindExnV values run
            · simp [typeError] at run
      | handle body rows =>
        rw [evaluate, (fixClockEvaluate st env [body] []).1] at run
        cases bodyRun : evaluate st env [body] with
        | mk middle bodyResult =>
          rw [bodyRun] at run
          cases bodyResult with
          | val bodyValues =>
            have length := evaluateLengthFull st middle env [body] bodyValues bodyRun
            simp only [Prod.mk.injEq, Result.val.injEq] at run
            rw [← run.2]
            exact length
          | err error =>
            cases error with
            | abort error => simp at run
            | raise errorValue =>
              have bound := evaluateClockFull st middle env [body] (.err (.raise errorValue)) bodyRun
              dsimp only at run
              split at run
              · exact evaluateMatchLengthFull middle next env errorValue rows errorValue values run
              · simp [typeError] at run
      | app op args =>
        rw [evaluate, (fixClockEvaluate st env args.reverse []).1] at run
        cases argsRun : evaluate st env args.reverse with
        | mk middle argsResult =>
          rw [argsRun] at run
          cases argsResult with
          | err error => simp at run
          | val argsValues =>
            have bound := evaluateClockFull st middle env args.reverse (.val argsValues) argsRun
            dsimp only at run
            cases opClass : getOpClass op with
            | funApp =>
              rw [opClass] at run
              dsimp only at run
              cases applied : doOpApp argsValues.reverse with
              | none => rw [applied] at run; simp [typeError] at run
              | some call =>
                obtain ⟨callEnv, body⟩ := call
                rw [applied] at run
                dsimp only at run
                split at run
                · simp [timeoutError] at run
                · exact evaluateLengthFull (decClock middle) next callEnv [body] values run
            | force =>
              rw [opClass] at run
              dsimp only at run
              cases thunk : destThunk argsValues.reverse middle.refs with
              | badRef => rw [thunk] at run; simp [typeError] at run
              | notThunk => rw [thunk] at run; simp [typeError] at run
              | isThunk mode value =>
                rw [thunk] at run
                cases mode with
                | evaluated => simp at run; simp [← run.2]
                | notEvaluated =>
                  dsimp only at run
                  cases applied : doOpApp [value, .conv none []] with
                  | none => rw [applied] at run; simp [typeError] at run
                  | some call =>
                    obtain ⟨callEnv, body⟩ := call
                    rw [applied] at run
                    dsimp only at run
                    split at run
                    · simp [timeoutError] at run
                    · cases bodyRun : evaluate (decClock middle) callEnv [body] with
                      | mk bodyState bodyResult =>
                        rw [bodyRun] at run
                        cases bodyResult with
                        | err error => simp at run
                        | val bodyValues =>
                          dsimp only at run
                          cases updated : updateThunk argsValues.reverse bodyState.refs bodyValues with
                          | none => rw [updated] at run; simp [typeError] at run
                          | some refs =>
                            rw [updated] at run
                            simp only [Prod.mk.injEq, Result.val.injEq] at run
                            have length := evaluateLengthFull (decClock middle) bodyState callEnv [body] bodyValues bodyRun
                            rw [← run.2]
                            exact length
            | evalOp =>
              rw [opClass] at run
              dsimp only at run
              repeat' first | split at run | simp_all [typeError, timeoutError]
              all_goals rw [← run.2]; rfl
            | simple =>
              rw [opClass] at run
              dsimp only at run
              cases applied : doApp (middle.refs, middle.ffi) op argsValues.reverse with
              | none => rw [applied] at run; simp [typeError] at run
              | some output =>
                obtain ⟨⟨refs, ffi⟩, result⟩ := output
                rw [applied] at run
                cases result with
                | val value => simp [listResult] at run; simp [← run.2]
                | err error => simp [listResult] at run
termination_by (st.clock, sizeOf expressions)
decreasing_by
  all_goals try subst_vars
  all_goals simp_wf
  all_goals try simp only [listSize_reverse]
  all_goals try simp only [Prod.lex_def, decClock]
  all_goals try (have := expSize_pos second)
  all_goals try (have := listSize_pos tail)
  all_goals try dsimp only [decClock] at *
  all_goals try simp only [Nat.lt_irrefl, false_or, true_and]
  all_goals try omega

/-- A successful source pattern match returns one value. -/
theorem evaluateMatchLengthFull {σ : Type} (st next : State σ) (env : SemEnv Value)
    (value : Value) (rows : List (Pat × AstHOL.Exp)) (errorValue : Value) (values : List Value)
    (run : evaluateMatch st env value rows errorValue = (next, .val values)) : values.length = 1 := by
  cases rows with
  | nil => simp [evaluateMatch] at run
  | cons row rest =>
    cases hrow : row with
    | mk pat body =>
      rw [hrow] at run
      rw [evaluateMatch] at run
      split at run
      · cases matched : pmatch env.c st.refs pat value [] with
        | typeError => simp [matched, typeError] at run
        | noMatch =>
          rw [matched] at run
          exact evaluateMatchLengthFull st next env value rest errorValue values run
        | «match» bindings =>
          rw [matched] at run
          exact evaluateLengthFull st next _ [body] values run
      · simp [typeError] at run
termination_by (st.clock, sizeOf rows)
decreasing_by
  all_goals try subst_vars
  all_goals simp_wf
  all_goals try simp only [Prod.lex_def]
  all_goals try (have := patSize_pos pat)
  all_goals try (have := listSize_pos rest)
  all_goals try simp_all
  all_goals omega
end

/-- A successful singleton expression evaluation returns exactly one value.
This corollary is Flapjack infrastructure; the HOL theorem's full source and
carrier correspondence review remains pending. -/
theorem evaluateSingFull {σ : Type} (st next : State σ) (env : SemEnv Value)
    (expr : AstHOL.Exp) (values : List Value)
    (run : evaluate st env [expr] = (next, .val values)) : ∃ value, values = [value] := by
  have length := evaluateLengthFull st next env [expr] values run
  cases values with
  | nil => simp at length
  | cons value tail =>
    cases tail with
    | nil => exact ⟨value, rfl⟩
    | cons head rest => simp at length

end Flapjack.EvaluateProps
