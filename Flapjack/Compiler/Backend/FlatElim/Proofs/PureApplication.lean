import Flapjack.Compiler.Backend.FlatElim.Proofs.PureState

/-! Constructor and global-initialization cases of pure flat evaluation. -/
namespace Flapjack.Compiler.Backend.FlatElim
open Flapjack.SemanticPrimitivesHOL

/-- The list purity analysis holds exactly when each expression is pure. -/
theorem allPure_iff (expressions : List FlatLang.Exp) :
    allPure expressions = true ↔ ∀ expression ∈ expressions, isPure expression = true := by
  induction expressions with
  | nil => simp [allPure]
  | cons first rest ih => simp [allPure, ih]

/-- Purity and Eval-freedom are preserved by reversing expression lists. -/
theorem pureArguments (args : List FlatLang.Exp) (pure : allPure args = true)
    (safe : hasEvalList args = false) :
    (∀ expression ∈ args.reverse, isPure expression = true) ∧ expressionsNoEval args.reverse := by
  constructor
  · intro expression member
    exact (allPure_iff args).mp pure expression (by simpa using member)
  · exact expressionsNoEval_reverse args ((hasEvalList_eq_false_iff args).mp safe)

/-- Empty location intersection for a constructor gives the same fact for
each argument, including in the evaluator's reverse order. -/
theorem constructorLocations (tra : BackendCommon.Tra) (constructor : Option (FlatLang.CtorId × FlatLang.TypeId))
    (args : List FlatLang.Exp) (reachable : NumSet)
    (empty : sptIsEmpty (sptInter (findLoc (.con tra constructor args)) reachable) = true) :
    ∀ expression ∈ args.reverse, sptIsEmpty (sptInter (findLoc expression) reachable) = true := by
  have argsEmpty : sptIsEmpty (sptInter (findGlobalsList destGlobalVarInit args) reachable) = true := by
    simpa [findLoc, findGlobals] using empty
  intro expression member
  exact findLocList_disjoint args reachable argsEmpty expression (by simpa using member)

/-- Constructor evaluation satisfies the pure-evaluation induction step. -/
theorem pureEvaluation_con {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source : FlatSem.State C F) (tra : BackendCommon.Tra)
    (constructor : Option (FlatLang.CtorId × FlatLang.TypeId)) (args : List FlatLang.Exp)
    (argsIH : pureEvaluationSimulationAt env source args.reverse) :
    pureEvaluationSimulationAt env source [.con tra constructor args] := by
  intro next result reachable target run expressionsPure envSafe expressionsSafe locationsEmpty related notTypeError
  have pure := expressionsPure (.con tra constructor args) (by simp)
  have safe := expressionsSafe (.con tra constructor args) (by simp)
  have empty := locationsEmpty (.con tra constructor args) (by simp)
  have argPure : allPure args = true := by simpa [isPure] using pure
  have argSafe : hasEvalList args = false := by simpa [hasEval] using safe
  have arguments := pureArguments args argPure argSafe
  cases evaluated : FlatSem.evaluate env source args.reverse with
  | mk argState argResult =>
    simp only [FlatSem.evaluate, evaluated] at run
    have argNotTypeError : argResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argResult
      simp at run
      rcases run with ⟨_, rfl⟩
      exact notTypeError rfl
    obtain ⟨values, nextRelated, resultEq, valuesSafe⟩ :=
      argsIH argState argResult reachable target evaluated arguments.1 envSafe arguments.2
        (constructorLocations tra constructor args reachable empty) related argNotTypeError
    subst argResult
    simp at run
    rcases run with ⟨rfl, rfl⟩
    have reversedSafe : valuesNoEval values.reverse := valuesNoEval_reverse values valuesSafe
    have valueSafe : valueHasEval (.conv constructor values.reverse) = false := by
      simpa [valueHasEval] using (valuesHaveEval_eq_false_iff _).mpr reversedSafe
    exact ⟨[.conv constructor values.reverse], nextRelated, rfl, by simpa [valuesNoEval] using valueSafe⟩

/-- An unreachable initialization has an unreachable destination and its
argument expressions do not initialize any reachable location. -/
theorem globalInitLocations (tra : BackendCommon.Tra) (index : Nat) (args : List FlatLang.Exp)
    (reachable : NumSet)
    (empty : sptIsEmpty (sptInter (findLoc (.app tra (.globalVarInit index) args)) reachable) = true) :
    ¬ sptMem index reachable ∧
      ∀ expression ∈ args.reverse, sptIsEmpty (sptInter (findLoc expression) reachable) = true := by
  have inserted : sptIsEmpty (sptInter (sptInsert index () (findGlobalsList destGlobalVarInit args)) reachable) = true := by
    simpa [findLoc, findGlobals, destGlobalVarInit] using empty
  have disjoint := (interEmpty_iff_disjoint _ _).mp inserted
  constructor
  · intro reachableIndex
    exact disjoint index ((sptMem_sptInsert index index () _).mpr (Or.inl rfl)) reachableIndex
  · intro expression member
    apply (interEmpty_iff_disjoint _ _).mpr
    intro key found reachableKey
    have inArgs := findLocList_member args expression (by simpa using member) key found
    exact disjoint key ((sptMem_sptInsert key index () _).mpr (Or.inr inArgs)) reachableKey

/-- Initializing an unreachable global satisfies the pure-evaluation induction
step when evaluation of its arguments satisfies that step. -/
theorem pureEvaluation_globalInit {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source : FlatSem.State C F) (tra : BackendCommon.Tra) (index : Nat) (args : List FlatLang.Exp)
    (argsIH : pureEvaluationSimulationAt env source args.reverse) :
    pureEvaluationSimulationAt env source [.app tra (.globalVarInit index) args] := by
  intro next result reachable target run expressionsPure envSafe expressionsSafe locationsEmpty related notTypeError
  have pure := expressionsPure (.app tra (.globalVarInit index) args) (by simp)
  have safe := expressionsSafe (.app tra (.globalVarInit index) args) (by simp)
  have empty := locationsEmpty (.app tra (.globalVarInit index) args) (by simp)
  have argPure : allPure args = true := by simpa [isPure] using pure
  have argSafe : hasEvalList args = false := by simpa [hasEval] using safe
  have arguments := pureArguments args argPure argSafe
  have locations := globalInitLocations tra index args reachable empty
  cases evaluated : FlatSem.evaluate env source args.reverse with
  | mk argState argResult =>
    simp only [FlatSem.evaluate, evaluated, FlatSem.fixClock] at run
    have argNotTypeError : argResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argResult
      simp at run
      rcases run with ⟨_, rfl⟩
      exact notTypeError rfl
    obtain ⟨values, argRelated, resultEq, _⟩ :=
      argsIH argState argResult reachable target evaluated arguments.1 envSafe arguments.2 locations.2 related argNotTypeError
    subst argResult
    have clocks : source.clock = argState.clock := related.1.trans argRelated.1.symm
    simp only [clocks, Nat.min_self] at run
    exact applyResult_globalInit_unreachable reachable argState target next index values.reverse result
      argRelated locations.1 run notTypeError

/-- If a union is disjoint from the reachable set, each component is disjoint. -/
theorem interEmpty_union (left right reachable : NumSet)
    (empty : sptIsEmpty (sptInter (sptUnion left right) reachable) = true) :
    sptIsEmpty (sptInter left reachable) = true ∧ sptIsEmpty (sptInter right reachable) = true := by
  have disjoint := (interEmpty_iff_disjoint _ _).mp empty
  constructor <;> apply (interEmpty_iff_disjoint _ _).mpr
  · intro key found reach
    exact disjoint key ((sptMem_sptUnion _ _ _).mpr (Or.inl found)) reach
  · intro key found reach
    exact disjoint key ((sptMem_sptUnion _ _ _).mpr (Or.inr found)) reach

end Flapjack.Compiler.Backend.FlatElim
