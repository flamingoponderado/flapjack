import Flapjack.Compiler.Backend.ClosCall.Proofs.ValueRelation

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
