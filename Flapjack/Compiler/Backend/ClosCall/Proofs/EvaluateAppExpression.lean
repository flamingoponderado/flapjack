module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.EvaluateApplication

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section

/-! Application-expression evaluation for direct-call conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

/-- The function and arguments of an application use only variables used by
the complete application. -/
theorem envRelFuel_app_parts {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {sourceEnv targetEnv : List ClosSem.Value}
    (trace : BackendCommon.Tra) (loc : Option Nat) (function : ClosLang.Exp) (arguments : List ClosLang.Exp)
    (related : EnvRelFuel fuel g allowed code sourceEnv targetEnv 0 [(0, .app trace loc function arguments)]) :
    EnvRelFuel fuel g allowed code sourceEnv targetEnv 0 [(0, function)] ∧
      EnvRelFuel fuel g allowed code sourceEnv targetEnv 0 (arguments.map (0, ·)) := by
  have h := (envRelFuel_iff _ _ _ _ _ _ _ _).mp related
  have make : ∀ fns, (∀ x, (∃ fn ∈ fns, ClosProps.freeVar (fn.1 + 0 + x) fn.2) →
      ClosProps.freeVarExp x function ∨ ClosProps.freeVars x arguments) →
      EnvRelFuel fuel g allowed code sourceEnv targetEnv 0 fns := by
    intro fns usedPart
    apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
    unfold envRel at h ⊢
    by_cases same : sourceEnv.length = targetEnv.length
    · simpa [same] using h
    simp only [same, ↓reduceIte] at h ⊢
    intro x used
    apply h x
    simp only [List.mem_singleton, exists_eq_left, Nat.zero_add,
      ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp, or_false]
    exact usedPart x used
  constructor
  · apply make
    intro x used
    simp only [List.mem_singleton, exists_eq_left, Nat.zero_add,
      ClosProps.freeVar, ClosProps.freeVars, or_false] at used
    exact Or.inl used
  · apply make
    intro x ⟨fn, member, free⟩
    obtain ⟨argument, inArgs, rfl⟩ := List.mem_map.mp member
    simp only [Nat.zero_add, ClosProps.freeVar, ClosProps.freeVars, or_false] at free
    exact Or.inr (freeVars_of_mem x argument arguments inArgs free)

/-- An application retained by the pass simulates when its argument list,
function expression, and selected closure bodies simulate. The separate
direct-call rewrite is not covered by this case. -/
theorem exprSimFuel_app {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (loc : Option Nat) (sourceFn targetFn : ClosLang.Exp)
    (sourceArgs targetArgs : List ClosLang.Exp) (length : sourceArgs.length = targetArgs.length)
    (distinct : (g.2.map Prod.fst).Nodup)
    (argsIH : ExprsSimFuel (C := C) (F := F) fuel g allowed sourceArgs targetArgs)
    (fnIH : ExprSimFuel (C := C) (F := F) fuel g allowed sourceFn targetFn)
    (bodyIH : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (sourceBody targetBody : ClosLang.Exp) (location : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
        (index arity : Nat),
      recClosureRelFuel fuel g allowed code location sourceFns targetFns →
      sourceFns[index]? = some (arity, sourceBody) → targetFns[index]? = some (arity, targetBody) →
      ExprSimFuel (C := C) (F := F) fuel g allowed sourceBody targetBody) :
    ExprSimFuel (C := C) (F := F) fuel g allowed
      (.app trace loc sourceFn sourceArgs) (.app trace loc targetFn targetArgs) := by
  intro sourceEnv targetEnv source target sourceResult sourceFinal run notType envs states
  obtain ⟨fnEnv, argsEnv⟩ := envRelFuel_app_parts trace loc targetFn targetArgs envs
  cases sourceArgs with
  | nil =>
    have bad : sourceResult = .err (.abort .typeError) := by
      simpa [evaluate] using congrArg Prod.fst run.symm
    exact False.elim (notType bad)
  | cons first rest =>
    have targetNonempty : targetArgs ≠ [] := by
      intro empty
      simp [empty] at length
    have targetNotEmpty : targetArgs.isEmpty = false := by
      cases targetArgs with
      | nil => exact False.elim (targetNonempty rfl)
      | cons head tail => rfl
    rw [evaluate] at run
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate] at run
    cases argsRun : evaluate (first :: rest) sourceEnv source with
    | mk argsResult argsFinal =>
      have argsNotType : argsResult ≠ .err (.abort .typeError) := by
        intro bad
        subst argsResult
        have : sourceResult = .err (.abort .typeError) := by
          simpa [argsRun] using congrArg Prod.fst run.symm
        exact notType this
      obtain ⟨targetArgsResult, targetArgsFinal, targetArgsRun, argsRel, argsStates, argsGrowth⟩ :=
        argsIH sourceEnv targetEnv source target argsResult argsFinal argsRun argsNotType argsEnv states
      cases argsResult with
      | err error =>
        cases targetArgsResult with
        | val values => simp [resultRel] at argsRel
        | err targetError =>
          have sourceEq : sourceResult = .err error ∧ sourceFinal = argsFinal := by
            simpa [argsRun] using run.symm
          obtain ⟨rfl, rfl⟩ := sourceEq
          refine ⟨.err targetError, targetArgsFinal, ?_, argsRel, argsStates, argsGrowth⟩
          rw [evaluate]
          simp only [targetNotEmpty, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate]
          rw [targetArgsRun]
      | val values =>
        cases targetArgsResult with
        | err error => simp [resultRel] at argsRel
        | val targetValues =>
          have valuesRel : List.Forall₂ (ValueRelFuel fuel g allowed targetArgsFinal.code) values targetValues := argsRel
          have fnEnv' : EnvRelFuel fuel g allowed targetArgsFinal.code sourceEnv targetEnv 0 [(0, targetFn)] :=
            envRelFuel_mono fnEnv (stateExtends_refl g distinct) Set.Subset.rfl argsGrowth
          cases fnRun : evaluate [sourceFn] sourceEnv argsFinal with
          | mk fnResult fnFinal =>
            have fnNotType : fnResult ≠ .err (.abort .typeError) := by
              intro bad
              subst fnResult
              have : sourceResult = .err (.abort .typeError) := by
                simpa [argsRun, fnRun, fixClock_evaluate] using congrArg Prod.fst run.symm
              exact notType this
            obtain ⟨targetFnResult, targetFnFinal, targetFnRun, fnRel, fnStates, fnGrowth⟩ :=
              fnIH sourceEnv targetEnv argsFinal targetArgsFinal fnResult fnFinal fnRun fnNotType fnEnv' argsStates
            cases fnResult with
            | err error =>
              cases targetFnResult with
              | val vs => simp [resultRel] at fnRel
              | err targetError =>
                have sourceEq : sourceResult = .err error ∧ sourceFinal = fnFinal := by
                  simpa [argsRun, fnRun, fixClock_evaluate] using run.symm
                obtain ⟨rfl, rfl⟩ := sourceEq
                refine ⟨.err targetError, targetFnFinal, ?_, fnRel, fnStates, ?_⟩
                · rw [evaluate]
                  simp only [targetNotEmpty, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate]
                  rw [targetArgsRun, targetFnRun]
                · intro key item lookup
                  exact fnGrowth key item (argsGrowth key item lookup)
            | val fnValues =>
              obtain ⟨fnValue, rfl⟩ := evaluate_singleton_value sourceFn sourceEnv argsFinal fnFinal fnValues fnRun
              cases targetFnResult with
              | err error => simp [resultRel] at fnRel
              | val targetFnValues =>
                obtain ⟨targetFnValue, rfl⟩ :=
                  evaluate_singleton_value targetFn targetEnv targetArgsFinal targetFnFinal targetFnValues targetFnRun
                have functionRel : ValueRelFuel fuel g allowed targetFnFinal.code fnValue targetFnValue := by
                  simpa [resultRel] using fnRel
                have valuesRel' : List.Forall₂ (ValueRelFuel fuel g allowed targetFnFinal.code) values targetValues :=
                  List.Forall₂.imp (fun _ _ h => valueRelFuel_mono h (stateExtends_refl g distinct) Set.Subset.rfl fnGrowth) valuesRel
                have appRun : evaluateApp loc fnValue values fnFinal = (sourceResult, sourceFinal) := by
                  simpa [argsRun, fnRun, fixClock_evaluate] using run
                obtain ⟨result, final, targetRun, results, finalStates, growth⟩ :=
                  appSimFuel_of_bodies fuel g allowed loc distinct bodyIH fnValue targetFnValue values targetValues
                    fnFinal targetFnFinal sourceResult sourceFinal appRun notType functionRel valuesRel' fnStates
                refine ⟨result, final, ?_, results, finalStates, ?_⟩
                · rw [evaluate]
                  simp only [targetNotEmpty, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate]
                  rw [targetArgsRun, targetFnRun]
                  simpa using targetRun
                · intro key item lookup
                  exact growth key item (fnGrowth key item (argsGrowth key item lookup))

/-- A location-free application stays an application in the direct-call pass.
Successful sub-traversals and their induction hypotheses yield its evaluation
simulation; known-location rewrites are a separate case. -/
theorem callsFuel_app_none_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp)
    (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.app trace none sourceFn sourceArgs) initial = some (out, final))
    (distinct : (g.2.map Prod.fst).Nodup)
    (argsIH : ∀ targetArgs middle, callsListFuel fuel sourceArgs initial = some (targetArgs, middle) →
      ExprsSimFuel (C := C) (F := F) fuel g allowed sourceArgs targetArgs)
    (fnIH : ∀ targetFn middle, callsFuel fuel sourceFn middle = some (targetFn, final) →
      ExprSimFuel (C := C) (F := F) fuel g allowed sourceFn targetFn)
    (bodyIH : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (sourceBody targetBody : ClosLang.Exp) (location : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
        (index arity : Nat),
      recClosureRelFuel fuel g allowed code location sourceFns targetFns →
      sourceFns[index]? = some (arity, sourceBody) → targetFns[index]? = some (arity, targetBody) →
      ExprSimFuel (C := C) (F := F) fuel g allowed sourceBody targetBody) :
    ∃ targetFn targetArgs, out = .app trace none targetFn targetArgs ∧
      ExprSimFuel (C := C) (F := F) fuel g allowed (.app trace none sourceFn sourceArgs)
        (.app trace none targetFn targetArgs) := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetArgs, middle⟩, argsRun, ⟨targetFn, next⟩, fnRun, rfl, rfl⟩ := run
  have length := callsListFuel_length fuel sourceArgs initial middle targetArgs argsRun
  refine ⟨targetFn, targetArgs, rfl, ?_⟩
  exact exprSimFuel_app fuel g allowed trace none sourceFn targetFn sourceArgs targetArgs length.symm distinct
    (argsIH targetArgs middle argsRun) (fnIH targetFn middle fnRun) bodyIH

/-- A location-annotated application also remains an application when its
location is absent from the pass state after visiting its arguments and
function. This is Lean-side case composition, not a standalone HOL theorem. -/
theorem callsFuel_app_unknown_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (loc : Nat) (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp)
    (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.app trace (some loc) sourceFn sourceArgs) initial = some (out, final))
    (unknown : sptLookup loc final.1 = none)
    (distinct : (g.2.map Prod.fst).Nodup)
    (argsIH : ∀ targetArgs middle, callsListFuel fuel sourceArgs initial = some (targetArgs, middle) →
      ExprsSimFuel (C := C) (F := F) fuel g allowed sourceArgs targetArgs)
    (fnIH : ∀ targetFn middle, callsFuel fuel sourceFn middle = some (targetFn, final) →
      ExprSimFuel (C := C) (F := F) fuel g allowed sourceFn targetFn)
    (bodyIH : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (sourceBody targetBody : ClosLang.Exp) (location : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
        (index arity : Nat),
      recClosureRelFuel fuel g allowed code location sourceFns targetFns →
      sourceFns[index]? = some (arity, sourceBody) → targetFns[index]? = some (arity, targetBody) →
      ExprSimFuel (C := C) (F := F) fuel g allowed sourceBody targetBody) :
    ∃ targetFn targetArgs, out = .app trace (some loc) targetFn targetArgs ∧
      ExprSimFuel (C := C) (F := F) fuel g allowed (.app trace (some loc) sourceFn sourceArgs)
        (.app trace (some loc) targetFn targetArgs) := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
  obtain ⟨⟨targetArgs, middle⟩, argsRun, ⟨targetFn, afterFn⟩, fnRun, rest⟩ := run
  by_cases found : (sptLookup loc afterFn.1).isSome
  · simp [found] at rest
    split at rest <;> simp_all
  · simp [found] at rest
    obtain ⟨rfl, rfl⟩ := rest
    have length := callsListFuel_length fuel sourceArgs initial middle targetArgs argsRun
    refine ⟨targetFn, targetArgs, rfl, ?_⟩
    exact exprSimFuel_app fuel g allowed trace (some loc) sourceFn targetFn sourceArgs targetArgs length.symm distinct
      (argsIH targetArgs middle argsRun) (fnIH targetFn middle fnRun) bodyIH

end Flapjack.Compiler.Backend.ClosCall
