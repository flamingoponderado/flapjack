import Flapjack.Compiler.Backend.ClosFvs.Proofs.EvaluateOp

/-! Mutual closure-application cases for free-variable removal. -/
namespace Flapjack.Compiler.Backend.ClosFvs
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Indexing related lists gives related optional entries. -/
theorem list_lookup_related {A B : Type} {relation : A → B → Prop} {left : List A} {right : List B}
    (related : List.Forall₂ relation left right) (index : Nat) :
    OptionRel relation left[index]? right[index]? := by
  induction related generalizing index with
  | nil => simp [OptionRel]
  | cons head tail ih =>
    cases index with
    | zero => simpa [OptionRel] using head
    | succ index => simpa using ih index

/-- Recursive closures generated from related bundles and environments are
related at each common index. -/
theorem recursive_bundle_related (location : Option Nat) (env nextEnv : List Value)
    (functions nextFunctions : List (Nat × ClosLang.Exp))
    (environments : List.Forall₂ ValueRel env nextEnv)
    (bodies : List.Forall₂ (FunctionRel (env.length + functions.length)) functions nextFunctions) :
    List.Forall₂ ValueRel
      ((List.range functions.length).map (fun i => Value.recclosure location [] env functions i))
      ((List.range nextFunctions.length).map (fun i => Value.recclosure location [] nextEnv nextFunctions i)) := by
  rw [← bodies.length_eq]
  generalize List.range functions.length = indices
  induction indices with
  | nil => exact .nil
  | cons index rest ih =>
    exact .cons (.recclosure location [] [] env nextEnv functions nextFunctions index environments .nil bodies) ih

/-- A successful closure inspection only accepts ordinary or recursive
closures. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "dest_closure_SOME_IMP"]
theorem destClosure_some_shape (maxApp : Nat) (location : Option Nat) (function : Value)
    (args : List Value) (result : AppKind) (run : destClosure maxApp location function args = some result) :
    (∃ loc supplied env arity body, function = .closure loc supplied env arity body) ∨
      (∃ loc supplied env functions index, function = .recclosure loc supplied env functions index) := by
  cases function <;> simp_all [destClosure]

/-- The ordinary-closure case of full application preserves the body relation,
the selected argument environment, and the over-application tail. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "dest_closure_SOME_Full_app"]
theorem destClosure_full_closure (maxApp : Nat) (requested location : Option Nat)
    (supplied nextSupplied env nextEnv : List Value) (arity : Nat) (body nextBody : ClosLang.Exp)
    (arg nextArg : Value) (args nextArgs : List Value) (resultBody : ClosLang.Exp)
    (resultEnv remaining : List Value)
    (envRel : List.Forall₂ ValueRel env nextEnv) (suppliedRel : List.Forall₂ ValueRel supplied nextSupplied)
    (bodyRel : CodeRel (env.length + arity) [body] [nextBody])
    (argRel : ValueRel arg nextArg) (argsRel : List.Forall₂ ValueRel args nextArgs)
    (run : destClosure maxApp requested (.closure location supplied env arity body) (arg :: args) =
      some (.fullApp resultBody resultEnv remaining)) :
    ∃ targetBody targetEnv targetRemaining,
      CodeRel resultEnv.length [resultBody] [targetBody] ∧ List.Forall₂ ValueRel resultEnv targetEnv ∧
      List.Forall₂ ValueRel remaining targetRemaining ∧
      destClosure maxApp requested (.closure location nextSupplied nextEnv arity nextBody) (nextArg :: nextArgs) =
        some (.fullApp targetBody targetEnv targetRemaining) := by
  have allArgs : List.Forall₂ ValueRel (arg :: args) (nextArg :: nextArgs) := .cons argRel argsRel
  by_cases valid : checkLoc maxApp requested location arity (arg :: args).length supplied.length = true ∧
      supplied.length < arity
  · by_cases partialCase : (arg :: args).length + supplied.length < arity
    · rw [destClosure_closure_source, if_pos valid, if_neg (not_not.mpr partialCase)] at run
      cases run
    · rw [destClosure_closure_source, if_pos valid, if_pos partialCase] at run
      simp only [Option.some.injEq, AppKind.fullApp.injEq] at run
      obtain ⟨rfl, rfl, rfl⟩ := run
      let needed := arity - supplied.length
      refine ⟨nextBody, ((nextArg :: nextArgs).reverse.take needed).reverse ++ (nextSupplied ++ nextEnv),
        ((nextArg :: nextArgs).reverse.drop needed).reverse, ?_, ?_, ?_, ?_⟩
      · have enough : needed ≤ (arg :: args).length := by
          dsimp [needed]
          simp only [List.length_cons] at partialCase ⊢
          omega
        have enough' : needed ≤ args.length + 1 := by simpa using enough
        have resultLength : (((arg :: args).reverse.take needed).reverse ++ (supplied ++ env)).length =
            env.length + arity := by
          simp only [List.length_append, List.length_reverse, List.length_take, List.length_cons,
            Nat.min_eq_left enough']
          dsimp [needed]
          omega
        change CodeRel (((arg :: args).reverse.take needed).reverse ++ (supplied ++ env)).length [body] [nextBody]
        rw [resultLength]
        exact bodyRel
      · have prefixRel := List.rel_reverse (List.forall₂_take needed (List.rel_reverse allArgs))
        exact List.rel_append prefixRel (List.rel_append suppliedRel envRel)
      · exact List.rel_reverse (List.forall₂_drop needed (List.rel_reverse allArgs))
      · have targetValid : checkLoc maxApp requested location arity (nextArg :: nextArgs).length nextSupplied.length = true ∧
            nextSupplied.length < arity := by simpa [← allArgs.length_eq, ← suppliedRel.length_eq] using valid
        have targetFull : ¬ ((nextArg :: nextArgs).length + nextSupplied.length < arity) := by
          simpa [← allArgs.length_eq, ← suppliedRel.length_eq] using partialCase
        rw [destClosure_closure_source, if_pos targetValid, if_pos targetFull]
        simp [needed, ← suppliedRel.length_eq]
  · rw [destClosure_closure_source, if_neg valid] at run
    contradiction

namespace AppPort
/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Applying a related function to an empty argument list returns the
function unchanged, with its state unchanged. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "evaluate_remove_fvs"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_fvs_app_nil {C F : Type} (location : Option Nat)
    (function targetFunction : Value) (source : State C F) (result : Result (List Value) Value)
    (sourceNext : State C F) (targetArgs : List Value) (target : State C F)
    (premises : evaluateApp location function [] source = (result, sourceNext) ∧
      ValueRel function targetFunction ∧ List.Forall₂ ValueRel [] targetArgs ∧ StateRel source target) :
    ∃ targetResult targetNext,
      evaluateApp location targetFunction targetArgs target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, functions, args, states⟩ := premises
  cases args
  simp [evaluateApp] at run
  obtain ⟨rfl, rfl⟩ := run
  exact ⟨.val [targetFunction], target, by simp [evaluateApp], .cons functions .nil, states⟩
end AppPort

end Flapjack.Compiler.Backend.ClosFvs
