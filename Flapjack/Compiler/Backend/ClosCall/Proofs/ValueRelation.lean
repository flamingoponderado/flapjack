module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.RecClosureRelation
public import Flapjack.Compiler.Backend.ClosCall.Proofs.Environment
public import Flapjack.Compiler.Backend.Semantics.ClosSem
public import Flapjack.Compiler.Backend.Semantics.ClosProps.SimpleRelations

@[expose] public section

/-! Fuel-aware value relation for direct-call conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack

mutual
/-- Values related by direct-call conversion. Primitive values agree; blocks
are related elementwise; closures carry the fuel-aware recursive-closure and
environment relations. This is not tagged as HOL's value relation because
the recursive-closure relation still depends on the bounded traversal. -/
inductive ValueRelFuel (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) : ClosSem.Value → ClosSem.Value → Prop where
  | number (n : Int) : ValueRelFuel fuel g allowed code (.number n) (.number n)
  | word64 (w : BitVec 64) : ValueRelFuel fuel g allowed code (.word64 w) (.word64 w)
  | block {tag xs ys} : List.Forall₂ (ValueRelFuel fuel g allowed code) xs ys →
      ValueRelFuel fuel g allowed code (.block tag xs) (.block tag ys)
  | byteVector (bytes : List (BitVec 8)) :
      ValueRelFuel fuel g allowed code (.byteVector bytes) (.byteVector bytes)
  | refPtr (flag : Bool) (address : Nat) :
      ValueRelFuel fuel g allowed code (.refPtr flag address) (.refPtr flag address)
  | closure {loc xs ys env1 env2 arity body1 body2} :
      recClosureRelFuel fuel g allowed code loc [(arity, body1)] [(arity, body2)] →
      List.Forall₂ (ValueRelFuel fuel g allowed code) xs ys →
      EnvRelFuel fuel g allowed code env1 env2 0 [(arity, body2)] →
      ValueRelFuel fuel g allowed code (.closure (some loc) xs env1 arity body1)
        (.closure (some loc) ys env2 arity body2)
  | recclosure {loc xs ys env1 env2 fns1 fns2 index} :
      recClosureRelFuel fuel g allowed code loc fns1 fns2 →
      List.Forall₂ (ValueRelFuel fuel g allowed code) xs ys →
      EnvRelFuel fuel g allowed code env1 env2 fns2.length fns2 →
      ValueRelFuel fuel g allowed code (.recclosure (some loc) xs env1 fns1 index)
        (.recclosure (some loc) ys env2 fns2 index)

/-- Strictly positive presentation of the direct-call environment relation,
used mutually with `ValueRelFuel`. -/
inductive EnvRelFuel (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) :
    List ClosSem.Value → List ClosSem.Value → Nat → List (Nat × ClosLang.Exp) → Prop where
  | equalLength {env1 env2 offset fns} : env1.length = env2.length →
      List.Forall₂ (ValueRelFuel fuel g allowed code) env1 env2 →
      EnvRelFuel fuel g allowed code env1 env2 offset fns
  | unequalLength {env1 env2 offset fns} : env1.length ≠ env2.length →
      (∀ x, (∃ fn ∈ fns, ClosProps.freeVar (fn.1 + offset + x) fn.2) → x < env1.length) →
      (∀ x, (∃ fn ∈ fns, ClosProps.freeVar (fn.1 + offset + x) fn.2) → x < env2.length) →
      (∀ x, (used : ∃ fn ∈ fns, ClosProps.freeVar (fn.1 + offset + x) fn.2) →
        ∀ (left : x < env1.length) (right : x < env2.length),
          ValueRelFuel fuel g allowed code env1[x] env2[x]) →
      EnvRelFuel fuel g allowed code env1 env2 offset fns
end

/-- The strictly positive environment predicate has exactly the generic
environment relation's two branches. -/
theorem envRelFuel_iff (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (env1 env2 : List ClosSem.Value) (offset : Nat) (fns : List (Nat × ClosLang.Exp)) :
    EnvRelFuel fuel g allowed code env1 env2 offset fns ↔
      envRel (ValueRelFuel fuel g allowed code) env1 env2 offset fns := by
  constructor
  · intro related
    cases related with
    | equalLength same pointwise => simpa [envRel, same] using pointwise
    | unequalLength different left right selective =>
      simp only [envRel, different, ↓reduceIte]
      intro x used
      exact ⟨left x used, right x used, selective x used _ _⟩
  · intro related
    by_cases same : env1.length = env2.length
    · exact .equalLength same (by simpa [envRel, same] using related)
    · simp only [envRel, same, ↓reduceIte] at related
      apply EnvRelFuel.unequalLength same
      · intro x used
        exact (related x used).choose
      · intro x used
        exact (related x used).choose_spec.choose
      · intro x used left right
        obtain ⟨_, _, h⟩ := related x used
        exact h

/-- Build a fuel-related environment for arbitrary expressions from a
target witness for each source value. The independent proof that HOL's
well-formed values supply these witnesses is still required. -/
theorem envRelFuel_exists_of_values (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (env : List ClosSem.Value)
    (values : ∀ value ∈ env, ∃ target, ValueRelFuel fuel g allowed code value target) :
    ∃ target, ∀ offset fns, EnvRelFuel fuel g allowed code env target offset fns := by
  obtain ⟨target, related⟩ := envRel_exists_of_values (ValueRelFuel fuel g allowed code) env values
  exact ⟨target, fun offset fns => (envRelFuel_iff fuel g allowed code env target offset fns).mpr
    (related offset fns)⟩

/-- Related numbers have the same value. -/
theorem valueRelFuel_number_iff (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (n : Int) (target : ClosSem.Value) :
    ValueRelFuel fuel g allowed code (.number n) target ↔ target = .number n := by
  constructor
  · intro related
    cases related
    rfl
  · intro equal
    subst target
    exact .number n

/-- The block case preserves its tag and relates the fields elementwise. -/
theorem valueRelFuel_block_iff (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (tag : Nat)
    (fields : List ClosSem.Value) (target : ClosSem.Value) :
    ValueRelFuel fuel g allowed code (.block tag fields) target ↔
      ∃ fields', target = .block tag fields' ∧ List.Forall₂ (ValueRelFuel fuel g allowed code) fields fields' := by
  constructor
  · intro related
    cases related with
    | block values => exact ⟨_, rfl, values⟩
  · rintro ⟨fields', rfl, values⟩
    exact .block values

/-- Closures without a numbered location cannot satisfy this relation. -/
theorem valueRelFuel_noLocation (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (xs env : List ClosSem.Value)
    (arity : Nat) (body : ClosLang.Exp) (target : ClosSem.Value) :
    ¬ValueRelFuel fuel g allowed code (.closure none xs env arity body) target := by
  intro related
  cases related

/-- Extending compiler state, permitted locations and installed code preserves
the fuel-aware value relation, including nested captured environments. -/
theorem valueRelFuel_mono {fuel : Nat} {g g' : State} {allowed allowed' : Set Nat}
    {code code' : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {source target : ClosSem.Value}
    (related : ValueRelFuel fuel g allowed code source target)
    (stateGrowth : stateExtends g g') (allowedGrowth : allowed ⊆ allowed')
    (codeGrowth : ∀ key value, code.lookup key = some value → code'.lookup key = some value) :
    ValueRelFuel fuel g' allowed' code' source target := by
  refine ValueRelFuel.rec
    (motive_1 := fun x y _ => ∀ g' allowed' code', stateExtends g g' → allowed ⊆ allowed' →
      (∀ key value, code.lookup key = some value → code'.lookup key = some value) →
      ValueRelFuel fuel g' allowed' code' x y)
    (motive_2 := fun xs ys offset fns _ => ∀ g' allowed' code', stateExtends g g' → allowed ⊆ allowed' →
      (∀ key value, code.lookup key = some value → code'.lookup key = some value) →
      EnvRelFuel fuel g' allowed' code' xs ys offset fns)
    (motive_3 := fun xs ys _ => ∀ g' allowed' code', stateExtends g g' → allowed ⊆ allowed' →
      (∀ key value, code.lookup key = some value → code'.lookup key = some value) →
      List.Forall₂ (ValueRelFuel fuel g' allowed' code') xs ys)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ related g' allowed' code' stateGrowth allowedGrowth codeGrowth
  · intro n _ _ _ _ _ _
    exact .number n
  · intro w _ _ _ _ _ _
    exact .word64 w
  · intro tag xs ys values ih g' allowed' code' hs ha hc
    exact .block (ih g' allowed' code' hs ha hc)
  · intro bytes _ _ _ _ _ _
    exact .byteVector bytes
  · intro flag address _ _ _ _ _ _
    exact .refPtr flag address
  · intro loc xs ys env1 env2 arity body1 body2 closure args env argsIH envIH g' allowed' code' hs ha hc
    exact .closure (recClosureRelFuel_mono fuel g g' allowed allowed' code code' loc _ _ closure hs ha hc)
      (argsIH g' allowed' code' hs ha hc) (envIH g' allowed' code' hs ha hc)
  · intro loc xs ys env1 env2 fns1 fns2 index closure args env argsIH envIH g' allowed' code' hs ha hc
    exact .recclosure (recClosureRelFuel_mono fuel g g' allowed allowed' code code' loc _ _ closure hs ha hc)
      (argsIH g' allowed' code' hs ha hc) (envIH g' allowed' code' hs ha hc)
  · intro env1 env2 offset fns same pointwise ih g' allowed' code' hs ha hc
    exact .equalLength same (ih g' allowed' code' hs ha hc)
  · intro env1 env2 offset fns different left right selective ih g' allowed' code' hs ha hc
    apply EnvRelFuel.unequalLength different left right
    intro x used l r
    exact ih x used l r g' allowed' code' hs ha hc
  · intro _ _ _ _ _ _
    exact .nil
  · intro a b xs ys head tail headIH tailIH g' allowed' code' hs ha hc
    exact .cons (headIH g' allowed' code' hs ha hc) (tailIH g' allowed' code' hs ha hc)

/-- The value relation has the constructor shape required by the generic
closure-language primitive-operation simulation. -/
theorem valueRelFuel_simple (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) :
    ClosProps.simpleValRel (ValueRelFuel fuel g allowed code) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x n
    constructor
    · intro related
      cases related
      rfl
    · intro equal
      subst x
      exact .number n
  · intro x fields tag
    constructor
    · intro related
      cases related with
      | block values => exact ⟨_, rfl, values⟩
    · rintro ⟨xs, rfl, values⟩
      exact .block values
  · intro x word
    constructor
    · intro related
      cases related
      rfl
    · intro equal
      subst x
      exact .word64 word
  · intro x bytes
    constructor
    · intro related
      cases related
      rfl
    · intro equal
      subst x
      exact .byteVector bytes
  · intro x address flag
    constructor
    · intro related
      cases related
      rfl
    · intro equal
      subst x
      exact .refPtr flag address
  · intro body arity env args loc x related
    cases related
    trivial
  · intro index fns env args loc x related
    cases related
    trivial

end Flapjack.Compiler.Backend.ClosCall
