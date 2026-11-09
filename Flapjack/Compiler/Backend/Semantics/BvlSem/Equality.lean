import Flapjack.Compiler.Backend.Semantics.BvlSem.Value
import Flapjack.SemanticPrimitivesHOL.Operations
import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-! Reference-aware equality for BVL runtime values. -/
namespace Flapjack.Compiler.Backend.BvlSem
open Flapjack.SemanticPrimitivesHOL (EqResult)
open Classical
noncomputable section

/-- Flapjack lookup-and-support view of the BVL reference map. -/
structure RefsBroad (α : Type) where
  lookup : Nat → Option (Ref α)
  finiteSupport : ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys

private def toBroad {α : Type} (refs : HolFiniteMapExact Nat (Ref α)) : RefsBroad α :=
  ⟨refs.lookup, refs.finiteSupport⟩

private def ofBroad {α : Type} (refs : RefsBroad α) : HolFiniteMapExact Nat (Ref α) :=
  ⟨refs.lookup, refs.finiteSupport⟩

/-- The canonical finite-map parameter's lookup and support roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_doEq_refs
    {α : Type} (refs : HolFiniteMapExact Nat (Ref α)) (key : Nat) :
    (ofBroad (toBroad refs)).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs)).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) = refs := by
  cases refs
  exact ⟨rfl, rfl, rfl⟩

/-- The list equality function uses the same canonical reference-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_doEqList_refs
    {α : Type} (refs : HolFiniteMapExact Nat (Ref α)) (key : Nat) :
    (ofBroad (toBroad refs)).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs)).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) = refs := by
  cases refs
  exact ⟨rfl, rfl, rfl⟩

mutual
/-- Compare BVL values, including closure blocks and immutable byte arrays. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "do_eq_def"
  (fmap_as_finite_support_parameters := [refs])]
def doEq {α : Type} (refs : HolFiniteMapExact Nat (Ref α)) (first second : Value) : EqResult :=
  match first, second with
  | .number a, .number b => .val (decide (a = b))
  | .word64 a, .word64 b => .val (decide (a = b))
  | .refPtr a x, .refPtr b y =>
    if a && b then
      match refs.lookup x, refs.lookup y with
      | some (.byteArray true xs), some (.byteArray true ys) => .val (decide (xs = ys))
      | some (.byteArray true _), _ | _, some (.byteArray true _) => .typeError
      | _, _ => .val (decide (x = y))
    else .typeError
  | .block a xs, .block b ys =>
    if isClosure a xs ∨ isClosure b ys then
      if isClosure a xs ∧ isClosure b ys then .val true else .typeError
    else if a = b ∧ xs.length = ys.length then doEqList refs xs ys else .val false
  | _, _ => .typeError
termination_by sizeOf first

/-- Compare lists left to right, propagating the first unequal or ill-typed
result and returning false for different lengths. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "do_eq_def"
  (fmap_as_finite_support_parameters := [refs])]
def doEqList {α : Type} (refs : HolFiniteMapExact Nat (Ref α)) (first second : List Value) : EqResult :=
  match first, second with
  | [], [] => .val true
  | x :: xs, y :: ys => match doEq refs x y with
    | .val true => doEqList refs xs ys
    | result => result
  | _, _ => .val false
termination_by sizeOf first
end

end
end Flapjack.Compiler.Backend.BvlSem
