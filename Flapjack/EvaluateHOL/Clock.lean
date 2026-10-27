import Flapjack.EvaluateHOL.Definition

/-! Cases of the original source evaluator clock theorem. The assembling
clock theorem remains open; these are individual constructor cases. -/
namespace Flapjack.EvaluateHOL
open Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL Flapjack.AstHOL

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateClock_nil {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (result : Result (List Value) Value) (h : evaluate st env [] = (st', result)) :
    st'.clock ≤ st.clock := by
  have hs := congrArg Prod.fst h
  simp only [evaluate] at hs
  subst st'
  exact Nat.le_refl _

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateClock_lit {σ : Type} (st st' : State σ) (env : SemEnv Value) (lit : Lit)
    (result : Result (List Value) Value) (h : evaluate st env [.lit lit] = (st', result)) :
    st'.clock ≤ st.clock := by
  have hs := congrArg Prod.fst h
  simp only [evaluate] at hs
  subst st'
  exact Nat.le_refl _

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateClock_fun {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (name : VarN) (body : Flapjack.AstHOL.Exp) (result : Result (List Value) Value)
    (h : evaluate st env [.fn name body] = (st', result)) : st'.clock ≤ st.clock := by
  have hs := congrArg Prod.fst h
  simp only [evaluate] at hs
  subst st'
  exact Nat.le_refl _

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateClock_var {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (name : Ident ModN VarN) (result : Result (List Value) Value)
    (h : evaluate st env [.var name] = (st', result)) : st'.clock ≤ st.clock := by
  have hs := congrArg Prod.fst h
  simp only [evaluate] at hs
  split at hs <;> simp_all [typeError]

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateMatchClock_nil {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (value errorValue : Value) (result : Result (List Value) Value)
    (h : evaluateMatch st env value [] errorValue = (st', result)) : st'.clock ≤ st.clock := by
  have hs := congrArg Prod.fst h
  simp only [evaluateMatch] at hs
  subst st'
  exact Nat.le_refl _

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateDecsClock_nil {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (result : Result (SemEnv Value) Value) (h : evaluateDecs st env [] = (st', result)) :
    st'.clock ≤ st.clock := by
  have hs := congrArg Prod.fst h
  simp only [evaluateDecs] at hs
  subst st'
  exact Nat.le_refl _

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateDecsClock_tabbrev {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (loc : Flapjack.Misc.Location.Locs) (vars : List TvarN) (name : TypeN) (typ : AstT)
    (result : Result (SemEnv Value) Value)
    (h : evaluateDecs st env [.dtabbrev loc vars name typ] = (st', result)) : st'.clock ≤ st.clock := by
  have hs := congrArg Prod.fst h
  simp only [evaluateDecs] at hs
  subst st'
  exact Nat.le_refl _

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateClock_raise {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (expr : Flapjack.AstHOL.Exp) (result : Result (List Value) Value)
    (ih : ∀ next outcome, evaluate st env [expr] = (next, outcome) → next.clock ≤ st.clock)
    (h : evaluate st env [.raise expr] = (st', result)) : st'.clock ≤ st.clock := by
  have bound := ih (evaluate st env [expr]).1 (evaluate st env [expr]).2 (by
    cases evaluate st env [expr]
    rfl)
  have hs := congrArg Prod.fst h
  simp only [evaluate] at hs
  cases hv : (evaluate st env [expr]).2 <;> simp_all

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateClock_tannot {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (expr : Flapjack.AstHOL.Exp) (typ : AstT) (result : Result (List Value) Value)
    (ih : ∀ next outcome, evaluate st env [expr] = (next, outcome) → next.clock ≤ st.clock)
    (h : evaluate st env [.tannot expr typ] = (st', result)) : st'.clock ≤ st.clock := by
  simp only [evaluate] at h
  exact ih st' result h

@[hol "cakeml/semantics/evaluateScript.sml" "evaluate_clock"]
theorem evaluateClock_lannot {σ : Type} (st st' : State σ) (env : SemEnv Value)
    (expr : Flapjack.AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs) (result : Result (List Value) Value)
    (ih : ∀ next outcome, evaluate st env [expr] = (next, outcome) → next.clock ≤ st.clock)
    (h : evaluate st env [.lannot expr loc] = (st', result)) : st'.clock ≤ st.clock := by
  simp only [evaluate] at h
  exact ih st' result h

end Flapjack.EvaluateHOL
