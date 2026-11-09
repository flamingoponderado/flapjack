module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.ValueRelation
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Equality
public import Flapjack.Compiler.Backend.Semantics.ClosProps.DecodeRelations

@[expose] public section

/-! Primitive observations of values related by direct-call conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem

/-- Equality returns the same result for pairs of related values. -/
theorem valueRelFuel_doEq (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (left right left' right' : Value)
    (first : ValueRelFuel fuel g allowed code left left')
    (second : ValueRelFuel fuel g allowed code right right') :
    doEq left right = doEq left' right' :=
  (ClosProps.simpleValRel_doEq _ (valueRelFuel_simple fuel g allowed code)).1
    left' right' left right ⟨first, second⟩

/-- Equality of lists also returns the same result across the relation. -/
theorem valueRelFuel_doEqList (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (left right left' right' : List Value)
    (first : List.Forall₂ (ValueRelFuel fuel g allowed code) left left')
    (second : List.Forall₂ (ValueRelFuel fuel g allowed code) right right') :
    doEqList left right = doEqList left' right' :=
  (ClosProps.simpleValRel_doEq _ (valueRelFuel_simple fuel g allowed code)).2
    left' right' left right ⟨first, second⟩

/-- Byte-list decoding is invariant under the value relation. -/
theorem valueRelFuel_toBytes (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (source target : Value)
    (related : ValueRelFuel fuel g allowed code source target) :
    valueToBytes source = valueToBytes target :=
  ClosProps.simpleValRel_valueToBytes _ source target ⟨valueRelFuel_simple fuel g allowed code, related⟩

/-- Word-list decoding is invariant under the value relation. -/
theorem valueRelFuel_toWords (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (source target : Value)
    (related : ValueRelFuel fuel g allowed code source target) :
    valueToWords source = valueToWords target :=
  ClosProps.simpleValRel_valueToWords source target _ ⟨valueRelFuel_simple fuel g allowed code, related⟩

end Flapjack.Compiler.Backend.ClosCall
