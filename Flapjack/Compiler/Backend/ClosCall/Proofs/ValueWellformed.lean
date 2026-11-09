module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.ValueRelation
public import Flapjack.Compiler.Backend.Semantics.ClosSem.Call
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section

/-! Fuel-aware well-formed values and related-value witnesses. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack

mutual
/-- Well-formedness corresponding to the shape of the source invariant,
using the bounded recursive-closure relation. It is not tagged as HOL's
definition because that relation still uses bounded traversal. -/
inductive ValueWellFormedFuel (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) : ClosSem.Value → Prop where
  | number (n : Int) : ValueWellFormedFuel fuel g allowed code (.number n)
  | word64 (w : BitVec 64) : ValueWellFormedFuel fuel g allowed code (.word64 w)
  | block (tag : Nat) {values} : ValuesWellFormedFuel fuel g allowed code values →
      ValueWellFormedFuel fuel g allowed code (.block tag values)
  | byteVector (bytes : List (BitVec 8)) : ValueWellFormedFuel fuel g allowed code (.byteVector bytes)
  | refPtr (flag : Bool) (address : Nat) : ValueWellFormedFuel fuel g allowed code (.refPtr flag address)
  | closure {loc supplied env arity body targets} :
      ValuesWellFormedFuel fuel g allowed code supplied → ValuesWellFormedFuel fuel g allowed code env →
      recClosureRelFuel fuel g allowed code loc [(arity, body)] targets →
      ValueWellFormedFuel fuel g allowed code (.closure (some loc) supplied env arity body)
  | recclosure {loc supplied env fns index targets} :
      ValuesWellFormedFuel fuel g allowed code supplied → ValuesWellFormedFuel fuel g allowed code env →
      recClosureRelFuel fuel g allowed code loc fns targets →
      ValueWellFormedFuel fuel g allowed code (.recclosure (some loc) supplied env fns index)

/-- Pointwise well-formed source values. -/
inductive ValuesWellFormedFuel (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) : List ClosSem.Value → Prop where
  | nil : ValuesWellFormedFuel fuel g allowed code []
  | cons {value values} : ValueWellFormedFuel fuel g allowed code value →
      ValuesWellFormedFuel fuel g allowed code values → ValuesWellFormedFuel fuel g allowed code (value :: values)
end

/-- Well-formed successful values and exception payloads; aborts have no
payload to check. This predicate is local to the fuel-aware simulation. -/
def ResultWellFormedFuel (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) :
    Flapjack.SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value → Prop
  | .val values => ValuesWellFormedFuel fuel g allowed code values
  | .err (.raise value) => ValueWellFormedFuel fuel g allowed code value
  | .err (.abort _) => True

/-- Extending compiler state, allowed locations, and installed code
preserves fuel-aware well-formedness of a value. -/
theorem valueWellFormedFuel_mono {fuel : Nat} {g g' : State} {allowed allowed' : Set Nat}
    {code code' : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {value : ClosSem.Value}
    (wf : ValueWellFormedFuel fuel g allowed code value)
    (stateGrowth : stateExtends g g') (allowedGrowth : allowed ⊆ allowed')
    (codeGrowth : ∀ key entry, code.lookup key = some entry → code'.lookup key = some entry) :
    ValueWellFormedFuel fuel g' allowed' code' value := by
  refine ValueWellFormedFuel.rec
    (motive_1 := fun value _ => ValueWellFormedFuel fuel g' allowed' code' value)
    (motive_2 := fun values _ => ValuesWellFormedFuel fuel g' allowed' code' values)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ wf
  · intro n; exact .number n
  · intro w; exact .word64 w
  · intro tag values _ ih; exact .block tag ih
  · intro bytes; exact .byteVector bytes
  · intro flag address; exact .refPtr flag address
  · intro loc supplied env arity body targets _ _ closure suppliedIH envIH
    exact .closure suppliedIH envIH
      (recClosureRelFuel_mono fuel g g' allowed allowed' code code' loc _ _ closure
        stateGrowth allowedGrowth codeGrowth)
  · intro loc supplied env fns index targets _ _ closure suppliedIH envIH
    exact .recclosure suppliedIH envIH
      (recClosureRelFuel_mono fuel g g' allowed allowed' code code' loc _ _ closure
        stateGrowth allowedGrowth codeGrowth)
  · exact .nil
  · intro value values _ _ headIH tailIH; exact .cons headIH tailIH

/-- The same extension preserves well-formedness of an environment. -/
theorem valuesWellFormedFuel_mono {fuel : Nat} {g g' : State} {allowed allowed' : Set Nat}
    {code code' : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {values : List ClosSem.Value}
    (wf : ValuesWellFormedFuel fuel g allowed code values)
    (stateGrowth : stateExtends g g') (allowedGrowth : allowed ⊆ allowed')
    (codeGrowth : ∀ key entry, code.lookup key = some entry → code'.lookup key = some entry) :
    ValuesWellFormedFuel fuel g' allowed' code' values := by
  induction values with
  | nil => exact .nil
  | cons value rest ih =>
    cases wf with
    | cons head tail =>
      exact .cons (valueWellFormedFuel_mono head stateGrowth allowedGrowth codeGrowth) (ih tail)

/-- Extending the compiler state, open locations, and installed code preserves
well-formed values or exception payloads in an evaluator result. This is
Flapjack-specific infrastructure. -/
theorem resultWellFormedFuel_mono {fuel : Nat} {g g' : State} {allowed allowed' : Set Nat}
    {code code' : HolFiniteMapExact Nat (Nat × ClosLang.Exp)}
    {result : Flapjack.SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value}
    (wf : ResultWellFormedFuel fuel g allowed code result)
    (stateGrowth : stateExtends g g') (allowedGrowth : allowed ⊆ allowed')
    (codeGrowth : ∀ key entry, code.lookup key = some entry → code'.lookup key = some entry) :
    ResultWellFormedFuel fuel g' allowed' code' result := by
  cases result with
  | val values =>
    exact valuesWellFormedFuel_mono wf stateGrowth allowedGrowth codeGrowth
  | err error =>
    cases error with
    | abort reason => trivial
    | raise value => exact valueWellFormedFuel_mono wf stateGrowth allowedGrowth codeGrowth

/-- Concatenation preserves pointwise value well-formedness. -/
theorem valuesWellFormedFuel_append {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {left right : List ClosSem.Value}
    (leftWf : ValuesWellFormedFuel fuel g allowed code left)
    (rightWf : ValuesWellFormedFuel fuel g allowed code right) :
    ValuesWellFormedFuel fuel g allowed code (left ++ right) := by
  induction left with
  | nil => exact rightWf
  | cons value rest ih =>
    cases leftWf with
    | cons head tail => exact .cons head (ih tail)

/-- A value present in a well-formed environment is well formed. -/
theorem valuesWellFormedFuel_mem {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {values : List ClosSem.Value}
    (wf : ValuesWellFormedFuel fuel g allowed code values) {value : ClosSem.Value}
    (member : value ∈ values) : ValueWellFormedFuel fuel g allowed code value := by
  induction values with
  | nil => simp at member
  | cons first rest ih =>
    cases wf with
    | cons head tail =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact head
      · exact ih tail member

/-- Pointwise well-formedness constructs a well-formed list. -/
theorem valuesWellFormedFuel_of_forall {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {values : List ClosSem.Value}
    (all : ∀ value ∈ values, ValueWellFormedFuel fuel g allowed code value) :
    ValuesWellFormedFuel fuel g allowed code values := by
  induction values with
  | nil => exact .nil
  | cons first rest ih =>
    refine .cons (all first (by simp)) (ih ?_)
    intro value member
    exact all value (by simp [member])

/-- Selecting environment variables preserves well-formedness, including
repeated indices and arbitrary selection order. -/
theorem lookupVars_wellFormedFuel {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (indices : List Nat)
    (env selected : List ClosSem.Value) (wf : ValuesWellFormedFuel fuel g allowed code env)
    (lookup : ClosSem.lookupVars indices env = some selected) :
    ValuesWellFormedFuel fuel g allowed code selected := by
  induction indices generalizing selected with
  | nil => simp [ClosSem.lookupVars] at lookup; subst selected; exact .nil
  | cons index rest ih =>
    simp only [ClosSem.lookupVars, Bind.bind, Option.bind_eq_some_iff, Option.some.injEq] at lookup
    obtain ⟨value, found, tail, tailFound, rfl⟩ := lookup
    have member : value ∈ env := by
      obtain ⟨bound, eq⟩ := List.getElem?_eq_some_iff.mp found
      simpa only [eq] using List.getElem_mem bound
    exact .cons (valuesWellFormedFuel_mem wf member) (ih tail tailFound)

/-- Closure environment restriction preserves well-formedness. -/
theorem closEnv_wellFormedFuel {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (restrict : Bool) (indices : List Nat)
    (env selected : List ClosSem.Value) (wf : ValuesWellFormedFuel fuel g allowed code env)
    (run : ClosSem.closEnv restrict indices env = some selected) :
    ValuesWellFormedFuel fuel g allowed code selected := by
  cases restrict with
  | false =>
    simp [ClosSem.closEnv] at run
    subst selected
    exact wf
  | true => exact lookupVars_wellFormedFuel indices env selected wf (by simpa [ClosSem.closEnv] using run)

/-- The bundle of recursive closures sharing a well-formed environment is
well formed at every generated index. -/
theorem recClosureBundle_wellFormedFuel {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (loc : Nat)
    (env : List ClosSem.Value) (fns targets : List (Nat × ClosLang.Exp))
    (envWf : ValuesWellFormedFuel fuel g allowed code env)
    (closure : recClosureRelFuel fuel g allowed code loc fns targets) :
    ValuesWellFormedFuel fuel g allowed code
      ((List.range fns.length).map (fun i => ClosSem.Value.recclosure (some loc) [] env fns i)) := by
  apply valuesWellFormedFuel_of_forall
  intro value member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact .recclosure .nil envWf closure

/-- Successful recursive-closure construction preserves well-formedness of
the selected environment and generated closure bundle. -/
theorem buildRecc_wellFormedFuel {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (restrict : Bool) (loc : Nat)
    (env : List ClosSem.Value) (indices : List Nat) (fns targets : List (Nat × ClosLang.Exp))
    (result : List ClosSem.Value) (envWf : ValuesWellFormedFuel fuel g allowed code env)
    (closure : recClosureRelFuel fuel g allowed code loc fns targets)
    (run : ClosSem.buildRecc restrict (some loc) env indices fns = some result) :
    ValuesWellFormedFuel fuel g allowed code result := by
  simp only [ClosSem.buildRecc, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq] at run
  obtain ⟨captured, captureRun, rfl⟩ := run
  exact recClosureBundle_wellFormedFuel loc captured fns targets
    (closEnv_wellFormedFuel restrict indices env captured envWf captureRun) closure

/-- Successful evaluation of a numbered function produces a well-formed
closure and leaves state unchanged, provided its function group satisfies
the bounded closure relation. -/
theorem evaluate_fn_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)}
    (name : Flapjack.Basis.Pure.MlString.MlString) (loc arity : Nat)
    (selected : Option (List Nat)) (body : ClosLang.Exp) (targets : List (Nat × ClosLang.Exp))
    (env : List ClosSem.Value) (state next : ClosSem.State C F) (value : ClosSem.Value)
    (envWf : ValuesWellFormedFuel fuel g allowed code env)
    (closure : recClosureRelFuel fuel g allowed code loc [(arity, body)] targets)
    (run : ClosSem.evaluate [.fn name (some loc) selected arity body] env state = (.val [value], next)) :
    ValueWellFormedFuel fuel g allowed code value ∧ next = state := by
  by_cases valid : arity ≤ state.maxApp ∧ arity ≠ 0
  · cases selected with
    | none =>
      simp [ClosSem.evaluate, valid] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨.closure .nil envWf closure, rfl⟩
    | some indices =>
      cases found : ClosSem.lookupVars indices env with
      | none => simp [ClosSem.evaluate, valid, found] at run
      | some captured =>
        have capturedWf := lookupVars_wellFormedFuel indices env captured envWf found
        simp [ClosSem.evaluate, valid, found] at run
        obtain ⟨rfl, rfl⟩ := run
        exact ⟨.closure .nil capturedWf closure, rfl⟩
  · cases selected <;> simp [ClosSem.evaluate, valid] at run

/-- A numbered recursive binding preserves result well-formedness when its
body does so for well-formed environments. The closure relation is the
separate compiler-invariant premise needed to construct recursive values. -/
theorem evaluate_letrec_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)}
    (names : List Flapjack.Basis.Pure.MlString.MlString) (loc : Nat)
    (selected : Option (List Nat)) (fns targets : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp)
    (env : List ClosSem.Value) (state : ClosSem.State C F)
    (envWf : ValuesWellFormedFuel fuel g allowed code env)
    (closure : recClosureRelFuel fuel g allowed code loc fns targets)
    (bodyIH : ∀ bodyEnv, ValuesWellFormedFuel fuel g allowed code bodyEnv →
      ResultWellFormedFuel fuel g allowed code (ClosSem.evaluate [body] bodyEnv state).1) :
    ResultWellFormedFuel fuel g allowed code
      (ClosSem.evaluate [.letrec names (some loc) selected fns body] env state).1 := by
  rw [ClosSem.evaluate.eq_def]
  by_cases valid : fns.all (fun (arity, _) => arity ≤ state.maxApp && arity != 0) = true
  · simp only [valid, ↓reduceIte]
    cases selected with
    | none =>
      simp only
      apply bodyIH
      exact valuesWellFormedFuel_append (recClosureBundle_wellFormedFuel loc env fns targets envWf closure) envWf
    | some indices =>
      cases found : ClosSem.lookupVars indices env with
      | none => simp [found, ResultWellFormedFuel]
      | some captured =>
        simp only [found]
        apply bodyIH
        exact valuesWellFormedFuel_append
          (recClosureBundle_wellFormedFuel loc captured fns targets
            (lookupVars_wellFormedFuel indices env captured envWf found) closure) envWf
  · simp [valid, ResultWellFormedFuel]

/-- Variable evaluation returns a well-formed value, or a type-error abort
when the index is absent. -/
theorem evaluate_var_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (trace : BackendCommon.Tra) (index : Nat)
    (env : List ClosSem.Value) (state : ClosSem.State C F)
    (envWf : ValuesWellFormedFuel fuel g allowed code env) :
    ResultWellFormedFuel fuel g allowed code (ClosSem.evaluate [.var trace index] env state).1 := by
  cases lookup : env[index]? with
  | none => simp [ClosSem.evaluate, lookup, ResultWellFormedFuel]
  | some value =>
    have member : value ∈ env := by
      obtain ⟨bound, eq⟩ := List.getElem?_eq_some_iff.mp lookup
      simpa only [eq] using List.getElem_mem bound
    simpa [ClosSem.evaluate, lookup, ResultWellFormedFuel] using
      ValuesWellFormedFuel.cons (valuesWellFormedFuel_mem envWf member) .nil

/-- A list made from members of a well-formed list is well formed. -/
theorem valuesWellFormedFuel_of_subset {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {source result : List ClosSem.Value}
    (wf : ValuesWellFormedFuel fuel g allowed code source)
    (subset : ∀ value ∈ result, value ∈ source) : ValuesWellFormedFuel fuel g allowed code result := by
  induction result with
  | nil => exact .nil
  | cons value rest ih =>
    apply ValuesWellFormedFuel.cons
    · exact valuesWellFormedFuel_mem wf (subset value (by simp))
    · apply ih
      intro item member
      exact subset item (by simp [member])

/-- Taking, dropping, and reversing preserve well-formedness. -/
theorem valuesWellFormedFuel_take {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {values : List ClosSem.Value}
    (wf : ValuesWellFormedFuel fuel g allowed code values) (count : Nat) :
    ValuesWellFormedFuel fuel g allowed code (values.take count) := by
  apply valuesWellFormedFuel_of_subset wf
  intro value member
  exact List.mem_of_mem_take member

theorem valuesWellFormedFuel_drop {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {values : List ClosSem.Value}
    (wf : ValuesWellFormedFuel fuel g allowed code values) (count : Nat) :
    ValuesWellFormedFuel fuel g allowed code (values.drop count) := by
  apply valuesWellFormedFuel_of_subset wf
  intro value member
  exact List.mem_of_mem_drop member

theorem valuesWellFormedFuel_reverse {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {values : List ClosSem.Value}
    (wf : ValuesWellFormedFuel fuel g allowed code values) :
    ValuesWellFormedFuel fuel g allowed code values.reverse := by
  apply valuesWellFormedFuel_of_subset wf
  intro value member
  simpa using member

/-- A partial closure application preserves well-formedness when its
function and argument values are well formed. -/
theorem destClosure_partial_wellFormedFuel {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)}
    (maxApp : Nat) (requested : Option Nat) (function : ClosSem.Value)
    (args : List ClosSem.Value) (result : ClosSem.Value)
    (functionWf : ValueWellFormedFuel fuel g allowed code function)
    (argsWf : ValuesWellFormedFuel fuel g allowed code args)
    (run : ClosSem.destClosure maxApp requested function args = some (.partialApp result)) :
    ValueWellFormedFuel fuel g allowed code result := by
  cases functionWf with
  | number | word64 | block | byteVector | refPtr => simp [ClosSem.destClosure] at run
  | @closure loc supplied env arity body targets suppliedWf envWf closure =>
    simp only [ClosSem.destClosure] at run
    split at run
    · split at run
      · simp only [Option.some.injEq, ClosSem.AppKind.partialApp.injEq] at run
        subst result
        exact .closure (valuesWellFormedFuel_append argsWf suppliedWf) envWf closure
      · simp at run
    · simp at run
  | @recclosure loc supplied env fns index targets suppliedWf envWf closure =>
    cases lookup : fns[index]? with
    | none => simp [ClosSem.destClosure, lookup] at run
    | some entry =>
      rcases entry with ⟨arity, body⟩
      simp only [ClosSem.destClosure, lookup] at run
      split at run
      · split at run
        · simp only [Option.some.injEq, ClosSem.AppKind.partialApp.injEq] at run
          subst result
          exact .recclosure (valuesWellFormedFuel_append argsWf suppliedWf) envWf closure
        · simp at run
      · simp at run

/-- A full application produces a well-formed body environment and
well-formed remaining arguments, including recursive closure bindings. -/
theorem destClosure_full_wellFormedFuel {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)}
    (maxApp : Nat) (requested : Option Nat) (function : ClosSem.Value)
    (args env rest : List ClosSem.Value) (body : ClosLang.Exp)
    (functionWf : ValueWellFormedFuel fuel g allowed code function)
    (argsWf : ValuesWellFormedFuel fuel g allowed code args)
    (run : ClosSem.destClosure maxApp requested function args = some (.fullApp body env rest)) :
    ValuesWellFormedFuel fuel g allowed code env ∧ ValuesWellFormedFuel fuel g allowed code rest := by
  cases functionWf with
  | number | word64 | block | byteVector | refPtr => simp [ClosSem.destClosure] at run
  | @closure loc supplied captured arity expression targets suppliedWf envWf closure =>
    simp only [ClosSem.destClosure] at run
    split at run
    · split at run
      · simp at run
      · simp only [Option.some.injEq, ClosSem.AppKind.fullApp.injEq] at run
        obtain ⟨rfl, rfl, rfl⟩ := run
        constructor
        · exact valuesWellFormedFuel_append
            (valuesWellFormedFuel_reverse (valuesWellFormedFuel_take (valuesWellFormedFuel_reverse argsWf) _))
            (valuesWellFormedFuel_append suppliedWf envWf)
        · exact valuesWellFormedFuel_reverse (valuesWellFormedFuel_drop (valuesWellFormedFuel_reverse argsWf) _)
    · simp at run
  | @recclosure loc supplied captured fns index targets suppliedWf envWf closure =>
    cases lookup : fns[index]? with
    | none => simp [ClosSem.destClosure, lookup] at run
    | some entry =>
      rcases entry with ⟨arity, expression⟩
      simp only [ClosSem.destClosure, lookup] at run
      split at run
      · split at run
        · simp at run
        · simp only [Option.some.injEq, ClosSem.AppKind.fullApp.injEq] at run
          obtain ⟨rfl, rfl, rfl⟩ := run
          constructor
          · exact valuesWellFormedFuel_append
              (valuesWellFormedFuel_reverse (valuesWellFormedFuel_take (valuesWellFormedFuel_reverse argsWf) _))
              (valuesWellFormedFuel_append
                (valuesWellFormedFuel_append suppliedWf (recClosureBundle_wellFormedFuel loc captured fns targets envWf closure)) envWf)
          · exact valuesWellFormedFuel_reverse (valuesWellFormedFuel_drop (valuesWellFormedFuel_reverse argsWf) _)
      · simp at run

/-- Every fuel-well-formed value has a target witness. This bounded theorem
does not claim the unbounded HOL value relation. -/
theorem valueRelFuel_exists {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {value : ClosSem.Value}
    (wf : ValueWellFormedFuel fuel g allowed code value) :
    ∃ target, ValueRelFuel fuel g allowed code value target := by
  refine ValueWellFormedFuel.rec
    (motive_1 := fun value _ => ∃ target, ValueRelFuel fuel g allowed code value target)
    (motive_2 := fun values _ => ∃ targets, List.Forall₂ (ValueRelFuel fuel g allowed code) values targets)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ wf
  · intro n; exact ⟨_, .number n⟩
  · intro w; exact ⟨_, .word64 w⟩
  · intro tag items _ ih
    obtain ⟨targets, related⟩ := ih
    exact ⟨_, .block related⟩
  · intro bytes; exact ⟨_, .byteVector bytes⟩
  · intro flag address; exact ⟨_, .refPtr flag address⟩
  · intro loc supplied env arity body targets _ _ closure suppliedIH envIH
    obtain ⟨targetSupplied, suppliedRel⟩ := suppliedIH
    obtain ⟨targetEnv, envRel⟩ := envIH
    obtain ⟨targetBody, rfl⟩ := recClosureRelFuel_singleton fuel g allowed code loc arity body targets closure
    exact ⟨_, .closure closure suppliedRel (.equalLength envRel.length_eq envRel)⟩
  · intro loc supplied env fns index targets _ _ closure suppliedIH envIH
    obtain ⟨targetSupplied, suppliedRel⟩ := suppliedIH
    obtain ⟨targetEnv, envRel⟩ := envIH
    exact ⟨_, .recclosure closure suppliedRel (.equalLength envRel.length_eq envRel)⟩
  · exact ⟨[], .nil⟩
  · intro value values _ _ headIH tailIH
    obtain ⟨target, headRel⟩ := headIH
    obtain ⟨targets, tailRel⟩ := tailIH
    exact ⟨target :: targets, .cons headRel tailRel⟩

/-- Construct related targets for a well-formed list. -/
theorem valuesRelFuel_exists {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {values : List ClosSem.Value}
    (wf : ValuesWellFormedFuel fuel g allowed code values) :
    ∃ targets, List.Forall₂ (ValueRelFuel fuel g allowed code) values targets := by
  induction values with
  | nil => exact ⟨[], .nil⟩
  | cons value rest ih =>
    cases wf with
    | cons head tail =>
      obtain ⟨target, headRel⟩ := valueRelFuel_exists head
      obtain ⟨targets, tailRel⟩ := ih tail
      exact ⟨target :: targets, .cons headRel tailRel⟩

/-- Every value occurring in a well-formed list has a related target. -/
theorem valuesWellFormedFuel_witnesses {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {values : List ClosSem.Value}
    (wf : ValuesWellFormedFuel fuel g allowed code values) :
    ∀ value ∈ values, ∃ target, ValueRelFuel fuel g allowed code value target := by
  induction values with
  | nil => simp
  | cons value rest ih =>
    cases wf with
    | cons head tail =>
      intro item member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact valueRelFuel_exists head
      · exact ih tail item member

/-- A well-formed source list admits an equally long related environment
for any requested function bodies. -/
theorem envRelFuel_exists_of_wellFormed (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (env : List ClosSem.Value)
    (wf : ValuesWellFormedFuel fuel g allowed code env) :
    ∃ target, target.length = env.length ∧
      ∀ offset fns, EnvRelFuel fuel g allowed code env target offset fns := by
  obtain ⟨target, related⟩ := valuesRelFuel_exists wf
  exact ⟨target, related.length_eq.symm, fun _ _ => .equalLength related.length_eq related⟩

end Flapjack.Compiler.Backend.ClosCall
