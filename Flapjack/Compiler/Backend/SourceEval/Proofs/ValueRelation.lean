import Flapjack.Compiler.Backend.SourceEval.Proofs.Environment
import Flapjack.Compiler.Backend.SourceEval.Proofs.OracleCallback
import Flapjack.SemanticPrimitivesHOL.Concrete
import Batteries.Data.List.Basic

/-! Relate source values before and after environment recording. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL Flapjack.AstHOL

mutual
/-- The source value relation. The mutually defined environment relation is a
positivity-friendly presentation of `envRel`; `valueEnvRel_iff` proves their
equivalence. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "v_rel"]
inductive ValueRel (state : EvalOracleState) : Value → Value → Prop where
  | env {env env' id encoded} (decoded : valueToEnvId encoded = some id)
      (lookup : lookupEnv state id = some env') (related : ValueEnvRel state env env') :
      ValueRel state (.env env id) encoded
  | vector {xs ys} (values : List.Forall₂ (ValueRel state) xs ys) :
      ValueRel state (.vectorv xs) (.vectorv ys)
  | con {xs ys stamp} (values : List.Forall₂ (ValueRel state) xs ys) :
      ValueRel state (.conv stamp xs) (.conv stamp ys)
  | closure {env env' name body} (related : ValueEnvRel state env env') :
      ValueRel state (.closure env name body) (.closure env' name body)
  | recclosure {env env' funs name} (related : ValueEnvRel state env env') :
      ValueRel state (.recclosure env funs name) (.recclosure env' funs name)
  | lit (lit) : ValueRel state (.litv lit) (.litv lit)
  | loc (flag index) : ValueRel state (.loc flag index) (.loc flag index)

/-- Flapjack's positivity-friendly form of the environment premise of `v_rel`;
the HOL original uses `env_rel` instead of a separate inductive relation. -/
inductive ValueEnvRel (state : EvalOracleState) : SemEnv Value → SemEnv Value → Prop where
  | intro {env env'} (constructors : env.c = env'.c) (domain : nsDom env.v = nsDom env'.v)
      (modules : nsDomMod env.v = nsDomMod env'.v)
      (values : ∀ name x y, nsLookup env.v name = some x ∧ nsLookup env'.v name = some y → ValueRel state x y) :
      ValueEnvRel state env env'
end

/-- The positivity-friendly environment relation has the original `env_rel`
shape. This bridge is Flapjack infrastructure, not a separate HOL theorem. -/
theorem valueEnvRel_iff (state : EvalOracleState) (env env' : SemEnv Value) :
    ValueEnvRel state env env' ↔ envRel (ValueRel state) env env' := by
  constructor
  · intro h
    cases h with
    | intro constructors domain modules values => exact ⟨constructors, domain, modules, values⟩
  · intro h
    obtain ⟨constructors, domain, modules, values⟩ := h
    exact .intro constructors domain modules values

/-- The source-shaped cases of the inductive relation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "v_rel_cases"]
theorem valueRel_hol_cases (state : EvalOracleState) (a b : Value) :
    ValueRel state a b ↔
      (∃ env id env', a = .env env id ∧ valueToEnvId b = some id ∧
        lookupEnv state id = some env' ∧ envRel (ValueRel state) env env') ∨
      (∃ xs ys, a = .vectorv xs ∧ b = .vectorv ys ∧ List.Forall₂ (ValueRel state) xs ys) ∨
      (∃ stamp xs ys, a = .conv stamp xs ∧ b = .conv stamp ys ∧ List.Forall₂ (ValueRel state) xs ys) ∨
      (∃ env env' name body, a = .closure env name body ∧ b = .closure env' name body ∧
        envRel (ValueRel state) env env') ∨
      (∃ env env' funs name, a = .recclosure env funs name ∧ b = .recclosure env' funs name ∧
        envRel (ValueRel state) env env') ∨
      (∃ lit, a = .litv lit ∧ b = .litv lit) ∨
      (∃ flag index, a = .loc flag index ∧ b = .loc flag index) := by
  constructor
  · intro related
    cases related with
    | env decoded lookup environments =>
      exact Or.inl ⟨_, _, _, rfl, decoded, lookup, (valueEnvRel_iff _ _ _).mp environments⟩
    | vector values => exact Or.inr (Or.inl ⟨_, _, rfl, rfl, values⟩)
    | con values => exact Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl, values⟩))
    | closure environments =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl, rfl, (valueEnvRel_iff _ _ _).mp environments⟩)))
    | recclosure environments =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl, rfl, (valueEnvRel_iff _ _ _).mp environments⟩))))
    | lit lit => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨lit, rfl, rfl⟩)))))
    | loc flag index => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨flag, index, rfl, rfl⟩)))))
  · rintro (⟨env, id, env', rfl, decoded, lookup, related⟩ |
      ⟨xs, ys, rfl, rfl, related⟩ | ⟨stamp, xs, ys, rfl, rfl, related⟩ |
      ⟨env, env', name, body, rfl, rfl, related⟩ |
      ⟨env, env', funs, name, rfl, rfl, related⟩ |
      ⟨lit, rfl, rfl⟩ | ⟨flag, index, rfl, rfl⟩)
    · exact .env decoded lookup ((valueEnvRel_iff _ _ _).mpr related)
    · exact .vector related
    · exact .con related
    · exact .closure ((valueEnvRel_iff _ _ _).mpr related)
    · exact .recclosure ((valueEnvRel_iff _ _ _).mpr related)
    · exact .lit lit
    · exact .loc flag index

/-- The mutual Lean relation satisfies HOL's generated induction scheme. This
bridge exposes its source-shaped nested environment and list premises. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "v_rel_ind"]
theorem valueRel_hol_induction (state : EvalOracleState) (P : Value → Value → Prop)
    (premises :
      (∀ env id encoded env', valueToEnvId encoded = some id ∧ lookupEnv state id = some env' ∧
        envRel P env env' → P (.env env id) encoded) ∧
      (∀ xs ys, List.Forall₂ P xs ys → P (.vectorv xs) (.vectorv ys)) ∧
      (∀ stamp xs ys, List.Forall₂ P xs ys → P (.conv stamp xs) (.conv stamp ys)) ∧
      (∀ env env' name body, envRel P env env' → P (.closure env name body) (.closure env' name body)) ∧
      (∀ env env' funs name, envRel P env env' → P (.recclosure env funs name) (.recclosure env' funs name)) ∧
      (∀ lit, P (.litv lit) (.litv lit)) ∧
      (∀ flag index, P (.loc flag index) (.loc flag index))) :
    ∀ a b, ValueRel state a b → P a b := by
  obtain ⟨envCase, vectorCase, conCase, closureCase, recclosureCase, litCase, locCase⟩ := premises
  intro a b related
  refine ValueRel.rec (motive_1 := fun a b _ => P a b)
    (motive_2 := fun env env' _ => envRel P env env')
    (motive_3 := fun xs ys _ => List.Forall₂ P xs ys) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ related
  · intro env env' id encoded decoded lookup _ ih
    exact envCase env id encoded env' ⟨decoded, lookup, ih⟩
  · intro xs ys _ ih
    exact vectorCase xs ys ih
  · intro xs ys stamp _ ih
    exact conCase stamp xs ys ih
  · intro env env' name body _ ih
    exact closureCase env env' name body ih
  · intro env env' funs name _ ih
    exact recclosureCase env env' funs name ih
  · exact litCase
  · exact locCase
  · intro env env' constructors domain modules _ ih
    exact ⟨constructors, domain, modules, ih⟩
  · exact .nil
  · intro a b xs ys _ _ ihA ihList
    exact .cons ihA ihList

mutual
private theorem concreteValueRel (state : EvalOracleState) (value : Value)
    (h : concreteValue value = true) : ValueRel state value value := by
  cases value with
  | litv lit => exact .lit lit
  | loc flag index => exact .loc flag index
  | conv stamp values => exact .con (concreteValuesRel state values (by simpa [concreteValue] using h))
  | vectorv values => exact .vector (concreteValuesRel state values (by simpa [concreteValue] using h))
  | closure _ _ _ | recclosure _ _ _ | env _ _ => simp [concreteValue] at h
termination_by sizeOf value

private theorem concreteValuesRel (state : EvalOracleState) (values : List Value)
    (h : concreteValues values = true) : List.Forall₂ (ValueRel state) values values := by
  cases values with
  | nil => exact .nil
  | cons value rest =>
    simp only [concreteValues, Bool.and_eq_true] at h
    exact .cons (concreteValueRel state value h.1) (concreteValuesRel state rest h.2)
termination_by sizeOf values
end

/-- Concrete values and concrete value lists are related to themselves. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "v_rel_concrete_v"]
theorem valueRel_concrete (state : EvalOracleState) :
    (∀ value, concreteValue value = true → ValueRel state value value) ∧
      (∀ values, concreteValues values = true → List.Forall₂ (ValueRel state) values values) :=
  ⟨concreteValueRel state, concreteValuesRel state⟩

/-- An environment containing only concrete values is related to itself. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "env_rel_concrete_v"]
theorem envRel_concrete (env : SemEnv Value) (state : EvalOracleState)
    (concrete : nsAll (fun _ value => concreteValue value = true) env.v) :
    envRel (ValueRel state) env env := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro name x y found
  have equal : x = y := Option.some.inj (found.1.symm.trans found.2)
  subst y
  exact (valueRel_concrete state).1 x (concrete name x found.1)

end Flapjack.Compiler.Backend.SourceEval.Proofs
