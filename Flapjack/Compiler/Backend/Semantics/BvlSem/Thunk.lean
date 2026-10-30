import Flapjack.Compiler.Backend.Semantics.BvlSem.State

/-! BVL thunk inspection and update restrictions. -/
namespace Flapjack.Compiler.Backend.BvlSem
open Flapjack.AstHOL (ThunkMode)

/-- Result of inspecting a possible BVL thunk reference. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "dest_thunk_ret"]
inductive DestThunkResult where
  | badRef
  | notThunk
  | isThunk : ThunkMode → Value → DestThunkResult

private def toBroad (refs : HolFiniteMapExact Nat (Ref Value)) : Nat → Option (Ref Value) := refs.lookup
private def ofBroad (lookup : Nat → Option (Ref Value))
    (support : ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact Nat (Ref Value) := ⟨lookup, support⟩

/-- Lookup and support roundtrip for the canonical thunk reference map. -/
theorem holFmapAsFiniteSupportParamWitness_destThunk_refs
    (refs : HolFiniteMapExact Nat (Ref Value)) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs := by
  cases refs
  exact ⟨rfl, rfl, rfl⟩

/-- The update restriction uses the same canonical reference-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_badThunkUpdate_refs
    (refs : HolFiniteMapExact Nat (Ref Value)) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs := by
  cases refs
  exact ⟨rfl, rfl, rfl⟩

/-- Inspect a value as a possible thunk pointer, retaining invalid-pointer
and non-thunk distinctions. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "dest_thunk_def"
  (fmap_as_finite_support_parameters := [refs])]
def destThunk (value : Value) (refs : HolFiniteMapExact Nat (Ref Value)) : DestThunkResult :=
  match value with
  | .refPtr flag index => match refs.lookup index with
    | none => .badRef
    | some (.thunk mode v) => if flag then .badRef else .isThunk mode v
    | some _ => .notThunk
  | _ => .notThunk

/-- An evaluated thunk cannot be updated to another thunk or a bad reference. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "bad_thunk_update_def"
  (fmap_as_finite_support_parameters := [refs])]
def badThunkUpdate (mode : ThunkMode) (value : Value) (refs : HolFiniteMapExact Nat (Ref Value)) : Prop :=
  mode = .evaluated ∧ destThunk value refs ≠ .notThunk

end Flapjack.Compiler.Backend.BvlSem
