module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationOpOrdinary

@[expose] public section


/-! Global-read replacement in known-function simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.Global
open ClosSem ClosProps ClosProps.StateGlobalSafety BackendProps
open OracleGlobals OracleMonotonic UniqueGlobalsPort StateOracleDisjoint SubsptComposition
open Relations Relations.StateRelation Relations.StateRelation.Oracle
open Flapjack.SemanticPrimitivesProps

/-- A global read can fail only with a type error. This is Flapjack proof
infrastructure for the optimizer's constant-replacement cases. -/
theorem globalReadError {C F : Type} (index : Nat) (values : List Value)
    (s : State C F) (error : Flapjack.SemanticPrimitivesHOL.ErrorResult Value)
    (run : doApp (.globOp (.global index)) values s = .err error) :
    error = .abort .typeError := by
  cases found : applyGlobal (.global index) values s with
  | none => simpa [doApp, found] using run.symm
  | some pair => simp [doApp, found] at run

/-- Simulate replacing a global read with an ordinary operation, given the
primitive-level replacement property. This is Flapjack induction infrastructure. -/
theorem globalReplacementSimulation {C F : Type} (c : Config) (tree : Spt ValApprox)
    (trace : BackendCommon.Tra) (index : Nat) (replacement : ClosLang.Op)
    (xs ys : List ClosLang.Exp) (env targetEnv : List Value)
    (s0 middle : State (Spt ValApprox × C) F) (t0 target : State C F)
    (argResult targetArgResult result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (final : State (Spt ValApprox × C) F)
    (notInstall : replacement ≠ .install) (notForce : replacement ≠ .thunkOp .forceThunk)
    (argsRun : evaluate xs env s0 = (argResult, middle))
    (targetArgsRun : evaluate ys targetEnv t0 = (targetArgResult, target))
    (states : StateRel c tree middle target)
    (argsRelated : resultRel (List.Forall₂ (ValueRel c tree)) (ValueRel c tree) argResult targetArgResult)
    (replace : ∀ vs ws next value, argResult = .val vs → List.Forall₂ (ValueRel c tree) vs.reverse ws →
      doApp (.globOp (.global index)) vs.reverse middle = .val (value, next) →
      next = middle ∧ doApp replacement ws target = .val (value, target) ∧ ValueRel c tree value value)
    (run : evaluate [.op trace (.globOp (.global index)) xs] env s0 = (result, final))
    (noType : result ≠ .err (.abort .typeError)) :
    ∃ result' targetFinal,
      evaluate [.op trace replacement ys] targetEnv t0 = (result', targetFinal) ∧
      resultRel (List.Forall₂ (ValueRel c tree)) (ValueRel c tree) result result' ∧
      StateRel c tree final targetFinal := by
  rw [evaluate_ordinaryOp_eq trace (.globOp (.global index)) xs env s0 (by simp) (by simp), argsRun] at run
  rw [evaluate_ordinaryOp_eq trace replacement ys targetEnv t0 notInstall notForce, targetArgsRun]
  cases argResult with
  | err error =>
    cases targetArgResult with
    | val values => simp [resultRel] at argsRelated
    | err other =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨.err other, target, rfl, argsRelated, states⟩
  | val values =>
    cases targetArgResult with
    | err error => simp [resultRel] at argsRelated
    | val targetValues =>
      cases app : doApp (.globOp (.global index)) values.reverse middle with
      | err error =>
        simp [app] at run
        rcases run with ⟨rfl, rfl⟩
        have eq := globalReadError index values.reverse middle error app
        subst error
        exact (noType rfl).elim
      | val pair =>
        rcases pair with ⟨value, next⟩
        simp [app] at run
        rcases run with ⟨rfl, rfl⟩
        obtain ⟨rfl, targetApp, related⟩ := replace values targetValues.reverse next value rfl
          (List.rel_reverse argsRelated) app
        dsimp only
        rw [targetApp]
        exact ⟨.val [value], target, rfl, .cons related .nil, states⟩

/-- Simulate the actual optimizer output for a global read, including
integer and empty-constructor replacement. This is Flapjack infrastructure. -/
theorem globalSelectedSimulation {C F : Type} (c : Config) (tree : Spt ValApprox)
    (trace : BackendCommon.Tra) (index : Nat) (a : ValApprox) (g0 g : Spt ValApprox)
    (argEas : List (ClosLang.Exp × ValApprox)) (xs : List ClosLang.Exp) (env targetEnv : List Value)
    (s0 middle : State (Spt ValApprox × C) F) (t0 target : State C F)
    (argResult targetArgResult result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (final : State (Spt ValApprox × C) F)
    (known : knownOpHOL (.globOp (.global index)) (argEas.map Prod.snd).reverse g0 = (a, g))
    (argsRun : evaluate xs env s0 = (argResult, middle))
    (targetArgsRun : evaluate (argEas.map Prod.fst) targetEnv t0 = (targetArgResult, target))
    (states : StateRel c tree middle target)
    (argsRelated : resultRel (List.Forall₂ (ValueRel c tree)) (ValueRel c tree) argResult targetArgResult)
    (argsApprox : ∀ values, argResult = .val values → List.Forall₂ ValApproxVal (argEas.map Prod.snd) values)
    (globals : stateGlobalsApprox middle g0)
    (run : evaluate [.op trace (.globOp (.global index)) xs] env s0 = (result, final))
    (noType : result ≠ .err (.abort .typeError)) :
    ∃ result' targetFinal,
      evaluate [Ordinary.selectedOutput trace (.globOp (.global index)) a (argEas.map Prod.fst)]
        targetEnv t0 = (result', targetFinal) ∧
      resultRel (List.Forall₂ (ValueRel c tree)) (ValueRel c tree) result result' ∧
      StateRel c tree final targetFinal := by
  have fallback := Relations.StateRelation.ordinarySmartOpSimulation c tree trace (.globOp (.global index))
    xs (argEas.map Prod.fst) env targetEnv s0 middle t0 target argResult targetArgResult
    (by simp) (by simp) argsRun targetArgsRun argsRelated states result final run noType
  cases a with
  | int i =>
    apply globalReplacementSimulation c tree trace index (.intOp (.const i)) xs (argEas.map Prod.fst)
      env targetEnv s0 middle t0 target argResult targetArgResult result final (by simp) (by simp)
      argsRun targetArgsRun states argsRelated ?_ run noType
    intro vs ws next value eq rel app
    have approx := List.rel_reverse (argsApprox vs eq)
    obtain ⟨_, _, _, stateEq, valueEq⟩ := knownGlobalIntShape index (argEas.map Prod.snd).reverse
      g0 g i vs.reverse middle next value known approx globals app
    have targetApp := (knownGlobalIntReplacement c tree index (argEas.map Prod.snd).reverse
      g0 g i vs.reverse ws middle next target value known approx rel globals app).2.2
    subst value
    exact ⟨stateEq, targetApp, .number i⟩
  | tuple tag elements =>
    cases elements with
    | nil =>
      apply globalReplacementSimulation c tree trace index (.blockOp (.cons tag)) xs (argEas.map Prod.fst)
        env targetEnv s0 middle t0 target argResult targetArgResult result final (by simp) (by simp)
        argsRun targetArgsRun states argsRelated ?_ run noType
      intro vs ws next value eq rel app
      have approx := List.rel_reverse (argsApprox vs eq)
      obtain ⟨_, _, _, stateEq, valueEq⟩ := knownGlobalEmptyTupleShape index (argEas.map Prod.snd).reverse
        g0 g tag vs.reverse middle next value known approx globals app
      have targetApp := (knownGlobalEmptyTupleReplacement c tree index (argEas.map Prod.snd).reverse
        g0 g tag vs.reverse ws middle next target value known approx rel globals app).2.2
      subst value
      exact ⟨stateEq, targetApp, .block tag [] [] .nil⟩
    | cons first rest => simpa [Ordinary.selectedOutput] using fallback
  | _ => simpa [Ordinary.selectedOutput] using fallback

end Flapjack.Compiler.Backend.ClosKnown.Simulation.Global
