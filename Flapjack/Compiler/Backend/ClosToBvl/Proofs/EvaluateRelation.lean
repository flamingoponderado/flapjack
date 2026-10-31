import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateVar
import Flapjack.SemanticPrimitivesProps.ResultRelation

/-! Source-shaped postconditions for closure-to-BVL evaluation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps
open Flapjack.Compiler.Backend.ClosProps

/-- Lookup characterization of finite-map extension, used for the relocation map. -/
def relocationSubmap (old new : HolFiniteMapExact Nat Nat) : Prop :=
  ∀ key value, old.lookup key = some value → new.lookup key = some value

/-- Lookup characterization of the source's submap between reference stores
after removing the respective relocation-map ranges. -/
def unmappedRefsSubmap
    (oldRefs newRefs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value))
    (oldMap newMap : HolFiniteMapExact Nat Nat) : Prop :=
  ∀ key value, oldRefs.lookup key = some value → (¬ ∃ n, oldMap.lookup n = some key) →
    newRefs.lookup key = some value ∧ (¬ ∃ n, newMap.lookup n = some key)

/-- Both source annotation predicates hold for each installed source function. -/
def codeAnnotations (s : ClosSem.State C F) : Prop :=
  (∀ name arity body, s.code.lookup name = some (arity, body) → everyFnLocationSome [body]) ∧
  (∀ name arity body, s.code.lookup name = some (arity, body) → everyFnVarsSome [body])

/-- Postcondition of the expression half of the source evaluation simulation.
This Flapjack infrastructure is untagged while the evaluators, state relation,
and finite-map ownership qualifier await source review. -/
def evaluatePost {C F : Type} (s sNext : ClosSem.State C F) (t : BvlSem.State C F)
    (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (result : Result (List ClosSem.Value) ClosSem.Value) (compiled : List Bvl.Exp) : Prop :=
  ∃ (extraClock : Nat) (targetResult : Result (List BvlSem.Value) BvlSem.Value)
    (tNext : BvlSem.State C F) (fNext : HolFiniteMapExact Nat Nat),
    BvlSem.evaluate compiled targetEnv { t with clock := s.clock + extraClock } = (targetResult, tNext) ∧
    resultRel (List.Forall₂ (vRel s.maxApp fNext tNext.refs tNext.code))
      (vRel s.maxApp fNext tNext.refs tNext.code) result targetResult ∧
    stateRel fNext sNext tNext ∧ relocationSubmap f fNext ∧
    unmappedRefsSubmap t.refs tNext.refs f fNext ∧ codeAnnotations sNext ∧
    sNext.clock = tNext.clock

/-- Empty expression lists satisfy the source-shaped evaluation postcondition.
This is a candidate case, not tagged as the HOL theorem while its evaluator and
state carriers remain unreviewed. -/
theorem evaluate_nil {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (s sNext : ClosSem.State C F) (t : BvlSem.State C F)
    (env : List ClosSem.Value) (targetEnv : List BvlSem.Value)
    (aux auxNext : List (Nat × Nat × Bvl.Exp)) (compiled : List Bvl.Exp)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate [] env s = (result, sNext))
    (_noTypeError : result ≠ .err (.abort .typeError))
    (compile : compileExpsHOL s.maxApp [] aux = (compiled, auxNext))
    (_locations : everyFnLocationSome []) (sourceAnnotations : codeAnnotations s)
    (_variables : everyFnVarsSome []) (_installed : codeInstalled auxNext t.code)
    (_envRelated : envRel s.maxApp f t.refs t.code env targetEnv)
    (statesRelated : stateRel f s t) : evaluatePost s sNext t targetEnv f result compiled := by
  simp [ClosSem.evaluate] at run
  simp [compileExpsHOL] at compile
  obtain ⟨resultEq, stateEq⟩ := run
  obtain ⟨compiledEq, _⟩ := compile
  subst result
  subst sNext
  subst compiled
  refine ⟨0, .val [], { t with clock := s.clock }, f, ?_, ?_, ?_, ?_, ?_, sourceAnnotations, rfl⟩
  · simp [BvlSem.evaluate]
  · exact List.Forall₂.nil
  · exact (stateRel_clock f s t s.clock).1.mpr statesRelated
  · intro key value lookup
    exact lookup
  · intro key value lookup fresh
    exact ⟨lookup, fresh⟩

/-- The variable case satisfies the same postcondition as the empty case,
including relocation and unmapped-reference preservation. It remains untagged
for the same evaluator and state-carrier review gaps as `evaluatePost`. -/
theorem evaluate_var_post {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (s sNext : ClosSem.State C F) (t : BvlSem.State C F)
    (env : List ClosSem.Value) (targetEnv : List BvlSem.Value)
    (trace : BackendCommon.Tra) (index : Nat)
    (aux auxNext : List (Nat × Nat × Bvl.Exp)) (compiled : List Bvl.Exp)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate [.var trace index] env s = (result, sNext))
    (noTypeError : result ≠ .err (.abort .typeError))
    (compile : compileExpsHOL s.maxApp [.var trace index] aux = (compiled, auxNext))
    (_locations : everyFnLocationSome [.var trace index]) (sourceAnnotations : codeAnnotations s)
    (_variables : everyFnVarsSome [.var trace index]) (_installed : codeInstalled auxNext t.code)
    (envRelated : envRel s.maxApp f t.refs t.code env targetEnv)
    (statesRelated : stateRel f s t) : evaluatePost s sNext t targetEnv f result compiled := by
  obtain ⟨value, targetValue, resultEq, stateEq, compilerEq, targetRun, valueRelated, nextStates⟩ :=
    evaluate_var f s t env targetEnv trace index aux result sNext run noTypeError envRelated statesRelated
  have compiledEq : compiled = [.var index] := congrArg Prod.fst (compile.symm.trans compilerEq)
  subst result
  subst sNext
  subst compiled
  refine ⟨0, .val [targetValue], { t with clock := s.clock }, f, ?_, ?_, nextStates, ?_, ?_,
    sourceAnnotations, rfl⟩
  · simpa using targetRun
  · exact List.Forall₂.cons valueRelated .nil
  · intro key value lookup
    exact lookup
  · intro key value lookup fresh
    exact ⟨lookup, fresh⟩

end Flapjack.Compiler.Backend.ClosToBvl
