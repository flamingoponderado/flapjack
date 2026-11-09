module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.PreservePure
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationAppPrefix
public import Flapjack.Compiler.Backend.Semantics.ClosProps.PureEvaluate

@[expose] public section


/-! Pure function-expression elimination in the inlining case. -/
namespace Flapjack.Compiler.Backend.ClosKnown.InlinePureEvaluation
open ClosSem ClosProps Relations PreservePure
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- If the function expression is pure, both the original and optimized
function evaluations return related singleton values without changing their
states. This is Flapjack infrastructure for eliminating that evaluation from
the generated let-binding. -/
theorem pureFunctionEvaluation {C F : Type} (c : Config) (x targetX : ClosLang.Exp)
    (env targetEnv : List ClosSem.Value) (aenv : List ValApprox)
    (g0 g1 current : Spt ValApprox) (a : ValApprox)
    (source next : State (Spt ValApprox × C) F) (target targetNext : State C F)
    (result targetResult : Result (List ClosSem.Value) ClosSem.Value)
    (known : knownListTotal c [x] aenv g0 = ([(targetX, a)], g1))
    (pure : ClosLang.pure x = true)
    (run : evaluate [x] env source = (result, next))
    (targetRun : evaluate [targetX] targetEnv target = (targetResult, targetNext))
    (related : resultRel (List.Forall₂ (ValueRel c current)) (ValueRel c current) result targetResult)
    (noType : result ≠ .err (.abort .typeError)) :
    ∃ fn targetFn, result = .val [fn] ∧ targetResult = .val [targetFn] ∧
      next = source ∧ targetNext = target ∧ ValueRel c current fn targetFn := by
  have sourcePure : ClosLang.pureList [x] = true := by simpa [ClosLang.pureList] using pure
  obtain ⟨values, sourceResult, sourceState⟩ := evaluate_pure [x] env source next result sourcePure run noType
  subst result
  obtain ⟨fn, rfl⟩ := evaluate_singleton_value x env source next values run
  cases targetResult with
  | err error => simp [resultRel] at related
  | val targetValues =>
    cases related with
    | cons fnRel rest =>
      cases rest
      have targetPure : ClosLang.pure targetX = true := by
        have all := knownPreservesPure c [x] aenv g0 [(targetX, a)] g1
          ⟨known, by simpa using pure⟩
        simpa using all
      have targetListPure : ClosLang.pureList [targetX] = true := by
        simpa [ClosLang.pureList] using targetPure
      obtain ⟨_, _, targetState⟩ := evaluate_pure [targetX] targetEnv target targetNext
        (.val [_]) targetListPure targetRun (by simp)
      exact ⟨fn, _, rfl, rfl, sourceState, targetState, fnRel⟩

end Flapjack.Compiler.Backend.ClosKnown.InlinePureEvaluation
