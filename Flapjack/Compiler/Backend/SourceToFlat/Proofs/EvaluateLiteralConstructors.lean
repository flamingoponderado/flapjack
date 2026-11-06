import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateSequence

/-! Constructor expressions with literal arguments in the preliminary
factored source-to-flat simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- Literal lists evaluate without changing the source state. -/
theorem evaluate_literalList {F : Type} (source : State F) (env : SemEnv Value) (lits : List Lit) :
    EvaluateHOL.evaluate source env (lits.map AstHOL.Exp.lit) = (source, .val (lits.map Value.litv)) := by
  induction lits with
  | nil => simp [EvaluateHOL.evaluate]
  | cons lit rest ih =>
    cases rest with
    | nil => simp [EvaluateHOL.evaluate]
    | cons next rest =>
      cases source
      simp [EvaluateHOL.evaluate, EvaluateHOL.fixClock, EvaluateHOL.headValue, Flapjack.holHd] at ih ⊢
      rw [ih]

/-- Compiled literal lists evaluate without changing the flat state. -/
theorem flatEvaluate_literalList {C F : Type} (flat : FlatSem.State C F) (env : FlatSem.Environment FlatSem.Value)
    (trace : List VarN) (compMap : Environment) (lits : List Lit) :
    FlatSem.evaluate env flat (compileExps trace compMap (lits.map AstHOL.Exp.lit)) =
      (flat, .val (lits.map FlatSem.Value.litv)) := by
  induction lits with
  | nil => simp [compileExps, FlatSem.evaluate]
  | cons lit rest ih =>
    cases rest with
    | nil => simp [compileExps, compileExp, FlatSem.evaluate]
    | cons next rest =>
      cases flat
      simp [compileExps, compileExp, FlatSem.evaluate, FlatSem.fixClock] at ih ⊢
      rw [ih]

/-- Literal argument lists satisfy the factored expression-list relation. -/
theorem exprListSim_literals {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (source : State F) (flat : FlatSem.State C F) (lits : List Lit)
    (states : StateRel genv source flat) :
    ExprListSim genv compMap trace sourceEnv flatEnv source flat (lits.map AstHOL.Exp.lit) := by
  unfold ExprListSim
  rw [evaluate_literalList, flatEvaluate_literalList]
  refine ⟨.value ?_, states⟩
  induction lits with
  | nil => exact .nil
  | cons lit rest ih => exact .cons (.literal genv lit) ih

/-- Pointwise expression simulations compose into an expression-list
simulation, including intermediate state changes and errors. -/
theorem exprListSim_of_expressions {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv Value) (flatEnv : FlatSem.Environment FlatSem.Value) (expressions : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ expressions → ∀ (source : State F) (flat : FlatSem.State C F),
      StateRel genv source flat → ExprSim genv compMap trace sourceEnv flatEnv source flat expr) :
    ∀ (source : State F) (flat : FlatSem.State C F), StateRel genv source flat →
      ExprListSim genv compMap trace sourceEnv flatEnv source flat expressions := by
  induction expressions with
  | nil =>
    intro source flat states
    simp only [ExprListSim, EvaluateHOL.evaluate, compileExps, FlatSem.evaluate]
    exact ⟨.value .nil, states⟩
  | cons head rest ih =>
    intro source flat states
    cases rest with
    | nil =>
      apply exprListSim_singleton
      exact each head (by simp) source flat states
    | cons next tail =>
      apply exprListSim_cons
      · exact each head (by simp) source flat states
      · intro nextSource nextFlat nextStates
        apply ih
        · intro expr member
          exact each expr (List.mem_cons_of_mem _ member)
        · exact nextStates

/-- If every singleton expression preserves the initial source state, their
sequential evaluation preserves it as well, including early errors. -/
theorem evaluateList_state_of_singletons {F : Type} (source : State F) (env : SemEnv Value)
    (expressions : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ expressions → (EvaluateHOL.evaluate source env [expr]).1 = source) :
    (EvaluateHOL.evaluate source env expressions).1 = source := by
  induction expressions with
  | nil => simp [EvaluateHOL.evaluate]
  | cons head rest ih =>
    cases rest with
    | nil => exact each head (by simp)
    | cons next tail =>
      have headState := each head (by simp)
      generalize headRun : EvaluateHOL.evaluate source env [head] = headResult at headState ⊢
      obtain ⟨nextState, headResult⟩ := headResult
      simp only at headState
      subst nextState
      have tailState := ih (fun expr member => each expr (List.mem_cons_of_mem _ member))
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source env [head] []).1, headRun]
      cases headResult with
      | err error => rfl
      | val values =>
        generalize tailRun : EvaluateHOL.evaluate source env (next :: tail) = tailResult at tailState ⊢
        obtain ⟨finalState, tailResult⟩ := tailResult
        simp only at tailState
        subst finalState
        cases tailResult <;> rfl

/-- The compiled expression list preserves its initial flat state when each
compiled singleton preserves it. -/
theorem flatEvaluateList_state_of_singletons {C F : Type} (flat : FlatSem.State C F)
    (flatEnv : FlatSem.Environment FlatSem.Value) (trace : List VarN) (compMap : Environment)
    (expressions : List AstHOL.Exp)
    (each : ∀ expr, expr ∈ expressions → (FlatSem.evaluate flatEnv flat [compileExp trace compMap expr]).1 = flat) :
    (FlatSem.evaluate flatEnv flat (compileExps trace compMap expressions)).1 = flat := by
  induction expressions with
  | nil => simp [compileExps, FlatSem.evaluate]
  | cons head rest ih =>
    cases rest with
    | nil => simpa [compileExps] using each head (by simp)
    | cons next tail =>
      have headState := each head (by simp)
      generalize headRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap head] = headResult at headState ⊢
      obtain ⟨nextState, headResult⟩ := headResult
      simp only at headState
      subst nextState
      have tailState := ih (fun expr member => each expr (List.mem_cons_of_mem _ member))
      simp only [compileExps]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat
        [compileExp trace compMap head] (FlatLang.Exp.lit .none (.intLit 0)) []).1, headRun]
      cases headResult with
      | err error => rfl
      | val values =>
        simp only [compileExps] at tailState
        generalize tailRun : FlatSem.evaluate flatEnv flat
          (compileExp trace compMap next :: compileExps trace compMap tail) = tailResult at tailState ⊢
        obtain ⟨finalState, tailResult⟩ := tailResult
        simp only at tailState
        subst finalState
        cases tailResult <;> rfl

/-- If a constructor's argument list preserves both evaluator states, the
constructor expression itself also preserves them, including error paths. -/
theorem constructor_states_of_args {C F : Type} (source : State F) (sourceEnv : SemEnv Value)
    (flat : FlatSem.State C F) (flatEnv : FlatSem.Environment FlatSem.Value)
    (trace : List VarN) (compMap : Environment) (name : Option (Ident ModN ConN)) (args : List AstHOL.Exp)
    (sourceSame : (EvaluateHOL.evaluate source sourceEnv args.reverse).1 = source)
    (flatSame : (FlatSem.evaluate flatEnv flat (compileExps trace compMap args).reverse).1 = flat) :
    (EvaluateHOL.evaluate source sourceEnv [.con name args]).1 = source ∧
      (FlatSem.evaluate flatEnv flat [compileExp trace compMap (.con name args)]).1 = flat := by
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv args.reverse = sourceResult at sourceSame ⊢
  obtain ⟨sourceNext, sourceResult⟩ := sourceResult
  simp only at sourceSame
  subst sourceNext
  generalize flatRun : FlatSem.evaluate flatEnv flat (compileExps trace compMap args).reverse = flatResult at flatSame ⊢
  obtain ⟨flatNext, flatResult⟩ := flatResult
  simp only at flatSame
  subst flatNext
  constructor
  · simp only [EvaluateHOL.evaluate]
    split
    · simp only [sourceRun]
      cases sourceResult with
      | err error => rfl
      | val values =>
        cases name with
        | none => simp [buildConv]
        | some id =>
          cases lookup : nsLookup sourceEnv.c id with
          | none => simp [buildConv, lookup, EvaluateHOL.typeError]
          | some pair => cases pair; simp [buildConv, lookup]
    · simp [EvaluateHOL.typeError]
  · simp only [compileExp, FlatSem.evaluate, flatRun]
    cases flatResult <;> rfl

end Flapjack.Compiler.Backend.SourceToFlat
