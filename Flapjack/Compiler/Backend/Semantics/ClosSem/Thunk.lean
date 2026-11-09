module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.State

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Thunk inspection and updates in the closure semantics. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.AstHOL

/-- Result of examining a possible thunk pointer. -/
@[hol "cakeml/compiler/backend/semantics/closSemScript.sml" "dest_thunk_ret"]
inductive DestThunkResult where
  | badRef
  | notThunk
  | isThunk : ThunkMode → Value → DestThunkResult

private def maptoBroadlookup {K V : Type} (map : HolFiniteMapExact K V) : K → Option V := map.lookup
private def mapofBroad {K V : Type} (lookup : K → Option V)
    (support : ∃ keys : List K, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact K V :=
  ⟨lookup, support⟩

/-- The reference-map lookup and finite-support representation roundtrips. -/
theorem holFmapAsFiniteSupportParamWitness_destThunk_refs (refs : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup refs) refs.finiteSupport = refs := by cases refs; rfl

/-- Inspect a singleton pointer, including the invalid-reference flag. -/
@[hol "cakeml/compiler/backend/semantics/closSemScript.sml" "dest_thunk_def"
  (fmap_as_finite_support_parameters := [refs])]
def destThunk (values : List Value) (refs : HolFiniteMapExact Nat (Ref Value)) : DestThunkResult :=
  match values with
  | [.refPtr isRef index] => match refs.lookup index with
    | none => .badRef
    | some (.thunk mode value) => if isRef then .badRef else .isThunk mode value
    | some _ => .notThunk
  | _ => .notThunk

/-- Update a thunk only if its previous mode is unevaluated. The key and
payload types are independent as in HOL. This remains untagged until a
qualifier for optional finite-map results is available. -/
noncomputable def storeThunkGeneral {κ α : Type} (index : κ) (value : Ref α) (refs : HolFiniteMapExact κ (Ref α)) :
    Option (HolFiniteMapExact κ (Ref α)) := by
  classical
  exact match refs.lookup index with
    | some (.thunk .notEvaluated _) => some (refs.updateEq (index, value))
    | _ => none

/-- Lookup-level form of the guarded thunk update, independent of the
finite-support representation. -/
noncomputable def storeThunkRaw {κ α : Type} (index : κ) (value : Ref α) (lookup : κ → Option (Ref α)) :
    Option (κ → Option (Ref α)) := by
  classical
  exact match lookup index with
    | some (.thunk .notEvaluated _) => some (fun key => if key = index then some value else lookup key)
    | _ => none

/-- Projecting the canonical map result agrees with the independent lookup
operation for every key and payload type. -/
theorem storeThunk_lookup {κ α : Type} (index : κ) (value : Ref α) (refs : HolFiniteMapExact κ (Ref α)) :
    (storeThunkGeneral index value refs).map (fun result => result.lookup) = storeThunkRaw index value refs.lookup := by
  classical
  unfold storeThunkGeneral storeThunkRaw
  split <;> simp_all [HolFiniteMapExact.updateEq]
  funext key
  simp [FUPDATE_HOL]

/-- The closure evaluator's computable natural-address specialization. -/
def storeThunk (index : Nat) (value : Ref Value) (refs : HolFiniteMapExact Nat (Ref Value)) :
    Option (HolFiniteMapExact Nat (Ref Value)) :=
  match refs.lookup index with
  | some (.thunk .notEvaluated _) => some (refs.updateEq (index, value))
  | _ => none

/-- The evaluator's specialized update agrees with the polymorphic one. -/
theorem storeThunk_eq_general (index : Nat) (value : Ref Value) (refs : HolFiniteMapExact Nat (Ref Value)) :
    storeThunk index value refs = storeThunkGeneral index value refs := by
  unfold storeThunk storeThunkGeneral
  split <;> simp_all
  congr 1
  congr 1
  funext x y
  exact Subsingleton.elim _ _

/-- An evaluated thunk cannot be updated to a thunk or invalid reference.
This remains untagged while its optional finite-map result is reviewed. -/
def updateThunk (targets : List Value) (refs : HolFiniteMapExact Nat (Ref Value))
    (values : List Value) : Option (HolFiniteMapExact Nat (Ref Value)) :=
  match targets, values with
  | [.refPtr false index], [value] => match destThunk [value] refs with
    | .notThunk => storeThunk index (.thunk .evaluated value) refs
    | _ => none
  | _, _ => none

/-- The reference-map lookup and finite-support representation roundtrips. -/
theorem holFmapAsFiniteSupportParamWitness_badThunkUpdate_refs (refs : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup refs) refs.finiteSupport = refs := by cases refs; rfl

/-- Test the original restriction on evaluated thunk contents. -/
@[hol "cakeml/compiler/backend/semantics/closSemScript.sml" "bad_thunk_update_def"
  (fmap_as_finite_support_parameters := [refs])]
def badThunkUpdate (mode : ThunkMode) (value : Value) (refs : HolFiniteMapExact Nat (Ref Value)) : Bool :=
  if mode = .evaluated then
    match destThunk [value] refs with
    | .notThunk => false
    | _ => true
  else false

end Flapjack.Compiler.Backend.ClosSem
