import Flapjack.Compiler.Backend.ClosCall.Proofs.InvariantDirectCall
import Flapjack.Compiler.Backend.ClosCall.Proofs.RecursiveInvariant

/-! Recursive binding simulation under the source invariants. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosProps ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

/-- A related recursive group enters the body with a well-formed source
environment. This bounded infrastructure is not the complete HOL theorem. -/
theorem evaluate_letrec_invariant_fuel {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (names : List Basis.Pure.MlString.MlString) (loc : Nat)
    (sourceFns targetFns : List (Nat × ClosLang.Exp)) (sourceBody targetBody : ClosLang.Exp)
    (bodyIH : ExprSimFuelInvariant (C := C) (F := F) fuel g allowed sourceBody targetBody)
    (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceResult : Result (List ClosSem.Value) ClosSem.Value) (sourceFinal : ClosSem.State (NumSet × C) F)
    (sourceRun : evaluate [.letrec names (some loc) none sourceFns sourceBody] sourceEnv source =
      (sourceResult, sourceFinal))
    (notType : sourceResult ≠ .err (.abort .typeError))
    (envs : EnvRelFuel fuel g allowed target.code sourceEnv targetEnv 0
      [(0, .letrec names (some loc) none targetFns targetBody)])
    (envWf : ValuesWellFormedFuel fuel g allowed target.code sourceEnv)
    (sourceWf : StateWellFormedFuel fuel g allowed target.code source)
    (states : StateRelFuel fuel g allowed source target)
    (closure : recClosureRelFuel fuel g allowed target.code loc sourceFns targetFns) :
    ∃ targetResult targetFinal,
      evaluate [.letrec names (some loc) none targetFns targetBody] targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel fuel g allowed targetFinal.code))
        (ValueRelFuel fuel g allowed targetFinal.code) sourceResult targetResult ∧
      StateRelFuel fuel g allowed sourceFinal targetFinal ∧
      (∀ key value, target.code.lookup key = some value → targetFinal.code.lookup key = some value) := by
  have valid : sourceFns.all (fun (arity, _) => arity ≤ source.maxApp && arity != 0) = true := by
    by_contra invalid
    have bad : sourceResult = .err (.abort .typeError) := by
      simpa [evaluate, invalid] using congrArg Prod.fst sourceRun.symm
    exact notType bad
  have targetValid : targetFns.all (fun (arity, _) => arity ≤ target.maxApp && arity != 0) = true := by
    have arities := recClosureRelFuel_arities fuel g allowed target.code loc sourceFns targetFns closure
    have same := congrArg (fun xs : List Nat => xs.all (fun arity => arity ≤ source.maxApp && arity != 0)) arities
    simp only [List.all_map, Function.comp_def] at same
    rw [← states.2.2.1, same]
    exact valid
  have bodyEnv := envRelFuel_letrec_enter names loc sourceFns targetFns targetBody closure envs
  have bodyRun : evaluate [sourceBody]
      ((List.range sourceFns.length).map (fun i => .recclosure (some loc) [] sourceEnv sourceFns i) ++ sourceEnv)
      source = (sourceResult, sourceFinal) := by
    simpa [evaluate, valid] using sourceRun
  have bodyEnvWf : ValuesWellFormedFuel fuel g allowed target.code
      ((List.range sourceFns.length).map (fun i => .recclosure (some loc) [] sourceEnv sourceFns i) ++ sourceEnv) :=
    valuesWellFormedFuel_append (recClosureBundle_wellFormedFuel loc sourceEnv sourceFns targetFns envWf closure) envWf
  obtain ⟨result, final, targetRun, results, finalStates, growth⟩ :=
    bodyIH _ _ source target sourceResult sourceFinal bodyRun notType bodyEnv bodyEnvWf sourceWf states
  refine ⟨result, final, ?_, results, finalStates, growth⟩
  simpa [evaluate, targetValid] using targetRun

/-- Source-driven recursive-binding evaluation after the actual pass run.
The body hypothesis is the local fuel-aware induction interface; the full
HOL simulation's oracle and growing-state conclusions remain open. -/
theorem callsFuel_letrec_invariant_evaluate {C F : Type} (fuel : Nat)
    (names : List Basis.Pure.MlString.MlString) (loc : Nat) (fns : List (Nat × ClosLang.Exp))
    (body out : ClosLang.Exp) (initial final g : State) (allowed : Set Nat)
    (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceResult : Result (List ClosSem.Value) ClosSem.Value) (sourceFinal : ClosSem.State (NumSet × C) F)
    (sourceRun : evaluate [.letrec names (some loc) none fns body] sourceEnv source = (sourceResult, sourceFinal))
    (notType : sourceResult ≠ .err (.abort .typeError))
    (run : callsFuel (fuel + 1) (.letrec names (some loc) none fns body) initial = some (out, final))
    (bodyIH : ∀ targetBody middle, callsFuel fuel body middle = some (targetBody, final) →
      ExprSimFuelInvariant (C := C) (F := F) fuel g allowed body targetBody)
    (initialWf : wellFormed initial)
    (locations : everyFnLocationSome [.letrec names (some loc) none fns body])
    (annotations : everyFnVarsNone [.letrec names (some loc) none fns body])
    (distinct : (codeLocations [.letrec names (some loc) none fns body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.letrec names (some loc) none fns body]) initial)
    (growth : stateExtends final g)
    (coverage : ∀ k ∈ codeLocations [.letrec names (some loc) none fns body],
      ¬ sptDomain final.1 k → k ∈ allowed)
    (included : codeIncludes g.2 target.code)
    (envs : EnvRelFuel fuel g allowed target.code sourceEnv targetEnv 0 [(0, out)])
    (envWf : ValuesWellFormedFuel fuel g allowed target.code sourceEnv)
    (sourceWf : StateWellFormedFuel fuel g allowed target.code source)
    (states : StateRelFuel fuel g allowed source target) :
    ∃ targetResult targetFinal,
      evaluate [out] targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel fuel g allowed targetFinal.code))
        (ValueRelFuel fuel g allowed targetFinal.code) sourceResult targetResult ∧
      StateRelFuel fuel g allowed sourceFinal targetFinal ∧
      (∀ key value, target.code.lookup key = some value → targetFinal.code.lookup key = some value) := by
  obtain ⟨targetFns, targetBody, middle, rfl, bodyRun, closure⟩ :=
    callsFuel_letrec_relation fuel names loc fns body out initial final g allowed target.code run initialWf
      locations annotations distinct fresh growth coverage included
  exact evaluate_letrec_invariant_fuel fuel g allowed names loc fns targetFns body targetBody (bodyIH targetBody middle bodyRun)
    sourceEnv targetEnv source target sourceResult sourceFinal sourceRun notType envs envWf sourceWf states closure

/-- Source evaluation of an actually traversed function preserves value and
state well-formedness when its generated code is included in the code map. -/
theorem callsFuel_fn_source_wellFormed {C F : Type} (fuel : Nat)
    (name : Basis.Pure.MlString.MlString) (loc arity : Nat) (body out : ClosLang.Exp)
    (initial final g : State) (allowed : Set Nat) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (env : List ClosSem.Value) (source : ClosSem.State (NumSet × C) F)
    (run : callsFuel (fuel + 1) (.fn name (some loc) none arity body) initial = some (out, final))
    (initialWf : wellFormed initial)
    (locations : everyFnLocationSome [.fn name (some loc) none arity body])
    (annotations : everyFnVarsNone [.fn name (some loc) none arity body])
    (distinct : (codeLocations [.fn name (some loc) none arity body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.fn name (some loc) none arity body]) initial)
    (growth : stateExtends final g)
    (coverage : ∀ k ∈ codeLocations [.fn name (some loc) none arity body],
      ¬ sptDomain final.1 k → k ∈ allowed)
    (included : codeIncludes final.2 code)
    (envWf : ValuesWellFormedFuel (fuel + 1) g allowed code env)
    (sourceWf : StateWellFormedFuel (fuel + 1) g allowed code source) :
    EvalWellFormedFuel (fuel + 1) g allowed code (evaluate [.fn name (some loc) none arity body] env source) := by
  obtain ⟨targetBody, _, closure⟩ := callsFuel_fn_relation fuel name loc arity body out
    initial final g allowed code run initialWf locations annotations distinct fresh growth coverage included
  exact evaluate_fn_state_wellFormedFuel name loc arity none body [(arity, targetBody)] env source envWf sourceWf closure

/-- Source evaluation of an actually traversed recursive binding preserves
well-formedness when its body does and its generated code is included. -/
theorem callsFuel_letrec_source_wellFormed {C F : Type} (fuel : Nat)
    (names : List Basis.Pure.MlString.MlString) (loc : Nat) (fns : List (Nat × ClosLang.Exp))
    (body out : ClosLang.Exp) (initial final g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (env : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F)
    (run : callsFuel (fuel + 1) (.letrec names (some loc) none fns body) initial = some (out, final))
    (initialWf : wellFormed initial)
    (locations : everyFnLocationSome [.letrec names (some loc) none fns body])
    (annotations : everyFnVarsNone [.letrec names (some loc) none fns body])
    (distinct : (codeLocations [.letrec names (some loc) none fns body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.letrec names (some loc) none fns body]) initial)
    (growth : stateExtends final g)
    (coverage : ∀ k ∈ codeLocations [.letrec names (some loc) none fns body],
      ¬ sptDomain final.1 k → k ∈ allowed)
    (included : codeIncludes g.2 code)
    (envWf : ValuesWellFormedFuel fuel g allowed code env)
    (sourceWf : StateWellFormedFuel fuel g allowed code source)
    (bodyWf : ∀ bodyEnv, ValuesWellFormedFuel fuel g allowed code bodyEnv →
      EvalWellFormedFuel fuel g allowed code (evaluate [body] bodyEnv source)) :
    EvalWellFormedFuel fuel g allowed code (evaluate [.letrec names (some loc) none fns body] env source) := by
  obtain ⟨targetFns, _, _, _, _, closure⟩ := callsFuel_letrec_relation fuel names loc fns body out
    initial final g allowed code run initialWf locations annotations distinct fresh growth coverage included
  exact evaluate_letrec_state_wellFormedFuel names loc none fns targetFns body env source envWf sourceWf closure bodyWf

/-- Source evaluation of a traversed function preserves well-formedness at
any independent relation fuel, provided its compiler state is extended and
its generated code is included. This is Flapjack-specific infrastructure. -/
theorem callsFuel_fn_source_wellFormed_atFuel {C F : Type} (traversalFuel relationFuel : Nat)
    (name : Basis.Pure.MlString.MlString) (loc arity : Nat) (body out : ClosLang.Exp)
    (initial final g : State) (allowed : Set Nat) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (env : List ClosSem.Value) (source : ClosSem.State (NumSet × C) F)
    (run : callsFuel (traversalFuel + 1) (.fn name (some loc) none arity body) initial = some (out, final))
    (initialWf : wellFormed initial)
    (locations : everyFnLocationSome [.fn name (some loc) none arity body])
    (annotations : everyFnVarsNone [.fn name (some loc) none arity body])
    (distinct : (codeLocations [.fn name (some loc) none arity body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.fn name (some loc) none arity body]) initial)
    (growth : stateExtends final g)
    (coverage : ∀ k ∈ codeLocations [.fn name (some loc) none arity body], ¬ sptDomain final.1 k → k ∈ allowed)
    (included : codeIncludes final.2 code)
    (envWf : ValuesWellFormedFuel relationFuel g allowed code env)
    (sourceWf : StateWellFormedFuel relationFuel g allowed code source) :
    EvalWellFormedFuel relationFuel g allowed code (evaluate [.fn name (some loc) none arity body] env source) := by
  obtain ⟨targetBody, _, closure⟩ := callsFuel_fn_relation_atFuel traversalFuel relationFuel name loc arity body out
    initial final g allowed code run initialWf locations annotations distinct fresh growth coverage included
  exact evaluate_fn_state_wellFormedFuel name loc arity none body [(arity, targetBody)] env source envWf sourceWf closure

/-- A traversed recursive binding has well-formed source evaluation at any
independent relation fuel when its actual continuation does. This is
Flapjack-specific infrastructure. -/
theorem callsFuel_letrec_source_wellFormed_atFuel {C F : Type} (traversalFuel relationFuel : Nat)
    (names : List Basis.Pure.MlString.MlString) (loc : Nat) (fns : List (Nat × ClosLang.Exp))
    (body out : ClosLang.Exp) (initial final g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (env : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F)
    (run : callsFuel (traversalFuel + 1) (.letrec names (some loc) none fns body) initial = some (out, final))
    (initialWf : wellFormed initial)
    (locations : everyFnLocationSome [.letrec names (some loc) none fns body])
    (annotations : everyFnVarsNone [.letrec names (some loc) none fns body])
    (distinct : (codeLocations [.letrec names (some loc) none fns body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.letrec names (some loc) none fns body]) initial)
    (growth : stateExtends final g)
    (coverage : ∀ k ∈ codeLocations [.letrec names (some loc) none fns body], ¬ sptDomain final.1 k → k ∈ allowed)
    (included : codeIncludes g.2 code)
    (envWf : ValuesWellFormedFuel relationFuel g allowed code env)
    (sourceWf : StateWellFormedFuel relationFuel g allowed code source)
    (bodyWf : ∀ bodyEnv, ValuesWellFormedFuel relationFuel g allowed code bodyEnv →
      EvalWellFormedFuel relationFuel g allowed code (evaluate [body] bodyEnv source)) :
    EvalWellFormedFuel relationFuel g allowed code (evaluate [.letrec names (some loc) none fns body] env source) := by
  obtain ⟨targetFns, _, _, _, _, closure⟩ := callsFuel_letrec_relation_atFuel traversalFuel relationFuel names loc fns body out
    initial final g allowed code run initialWf locations annotations distinct fresh growth coverage included
  exact evaluate_letrec_state_wellFormedFuel names loc none fns targetFns body env source envWf sourceWf closure bodyWf

/-- The source well-formedness case for recursive binding uses its actual
continuation traversal and inherits its syntax and coverage conditions.
The continuation's well-formedness remains an induction hypothesis. This is
Flapjack-specific infrastructure. -/
theorem callsFuel_letrec_source_wellFormed_from_continuation {C F : Type} (traversalFuel relationFuel : Nat)
    (names : List Basis.Pure.MlString.MlString) (loc : Nat) (fns : List (Nat × ClosLang.Exp))
    (body out : ClosLang.Exp) (initial final g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (env : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F)
    (run : callsFuel (traversalFuel + 1) (.letrec names (some loc) none fns body) initial = some (out, final))
    (initialWf : wellFormed initial)
    (locations : everyFnLocationSome [.letrec names (some loc) none fns body])
    (annotations : everyFnVarsNone [.letrec names (some loc) none fns body])
    (distinct : (codeLocations [.letrec names (some loc) none fns body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.letrec names (some loc) none fns body]) initial)
    (growth : stateExtends final g)
    (coverage : ∀ k ∈ codeLocations [.letrec names (some loc) none fns body], ¬ sptDomain final.1 k → k ∈ allowed)
    (included : codeIncludes g.2 code)
    (envWf : ValuesWellFormedFuel relationFuel g allowed code env)
    (sourceWf : StateWellFormedFuel relationFuel g allowed code source)
    (bodyIH : ∀ targetBody middle, callsFuel traversalFuel body middle = some (targetBody, final) →
      wellFormed middle → (codeLocationsExp body).Nodup → LabelsFresh (codeLocationsExp body) middle →
      everyFnLocationSome [body] → everyFnVarsNone [body] →
      (∀ k ∈ codeLocations [body], ¬ sptDomain final.1 k → k ∈ allowed) →
      ∀ bodyEnv, ValuesWellFormedFuel relationFuel g allowed code bodyEnv →
        EvalWellFormedFuel relationFuel g allowed code (evaluate [body] bodyEnv source)) :
    EvalWellFormedFuel relationFuel g allowed code (evaluate [.letrec names (some loc) none fns body] env source) := by
  obtain ⟨_, targetBody, middle, _, continuation, middleWf, bodyDistinct, bodyFresh⟩ :=
    callsFuel_letrec_continuation_wellFormed traversalFuel names loc fns body out initial final run
      initialWf locations annotations distinct fresh
  have bodyLocations : everyFnLocationSome [body] := by
    have h := locations
    simp [everyFnLocationSome, fnLocationSomeExp] at h
    simpa [everyFnLocationSome] using h.2
  have bodyAnnotations : everyFnVarsNone [body] := by
    have h := annotations
    simp [everyFnVarsNone, fnVarsNoneExp] at h
    simpa [everyFnVarsNone] using h.2
  have bodyCoverage : ∀ k ∈ codeLocations [body], ¬ sptDomain final.1 k → k ∈ allowed := by
    intro k member unknown
    apply coverage k ?_ unknown
    simp only [codeLocations, codeLocationsExp, List.append_nil, List.mem_append] at member ⊢
    tauto
  apply callsFuel_letrec_source_wellFormed_atFuel traversalFuel relationFuel names loc fns body out
    initial final g allowed code env source run initialWf locations annotations distinct fresh growth coverage included envWf sourceWf
  exact bodyIH targetBody middle continuation middleWf bodyDistinct bodyFresh bodyLocations bodyAnnotations bodyCoverage

end Flapjack.Compiler.Backend.ClosCall
