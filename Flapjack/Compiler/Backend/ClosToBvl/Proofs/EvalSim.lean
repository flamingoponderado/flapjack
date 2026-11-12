module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Semantics

@[expose] public section

/-! Representation infrastructure for the closure-to-BVL evaluation simulation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

private abbrev SimulationTail (C₁ C₂ : Type) := ClosSem.CompileOracle C₁ →
  ClosSem.Compiler C₁ → List ClosLang.Exp → Spt (Nat × Bvl.Exp) →
  BvlSem.CompileOracle C₂ → BvlSem.Compiler C₂ → Nat → Prop

private abbrev RawCode := Nat → Option (Nat × ClosLang.Exp)

private abbrev RawCodeSupport (lookup : RawCode) :=
  ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys

private def toBroad (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) : RawCode :=
  code.lookup

private def ofBroad (lookup : RawCode) (support : RawCodeSupport lookup) :
    HolFiniteMapExact Nat (Nat × ClosLang.Exp) := ⟨lookup, support⟩

private def toBroadPredicate {C₁ C₂ : Type}
    (rel : HolFiniteMapExact Nat (Nat × ClosLang.Exp) → SimulationTail C₁ C₂)
    (lookup : RawCode) (support : RawCodeSupport lookup) : SimulationTail C₁ C₂ :=
  rel (ofBroad lookup support)

private def fromBroadPredicate {C₁ C₂ : Type}
    (rel : (lookup : RawCode) → RawCodeSupport lookup → SimulationTail C₁ C₂)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) : SimulationTail C₁ C₂ :=
  rel (toBroad code) code.finiteSupport

/-- The two views transport an arbitrary simulation relation in both directions.
This is Flapjack representation infrastructure for the higher-order map argument
of `eval_sim`, rather than a separate HOL declaration. -/
theorem simulationPredicateRoundtrips {C₁ C₂ : Type} :
    (∀ (rel : HolFiniteMapExact Nat (Nat × ClosLang.Exp) → SimulationTail C₁ C₂)
      (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)),
      fromBroadPredicate (toBroadPredicate rel) code = rel code) ∧
    (∀ (rel : (lookup : RawCode) → RawCodeSupport lookup → SimulationTail C₁ C₂)
      (lookup : RawCode) (support : RawCodeSupport lookup),
      toBroadPredicate (fromBroadPredicate rel) lookup support = rel lookup support) := by
  constructor
  · intro rel code
    cases code
    rfl
  · intro rel lookup support
    rfl

end Flapjack.Compiler.Backend.ClosToBvl
