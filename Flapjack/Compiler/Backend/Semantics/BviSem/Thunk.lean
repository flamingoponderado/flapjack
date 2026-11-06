import Flapjack.Compiler.Backend.Semantics.BviSem.State
import Flapjack.Compiler.Backend.Semantics.BvlSem.Thunk

/-! BVI thunk inspection. -/
namespace Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem
open Flapjack.AstHOL (ThunkMode)

/-- The original BVI thunk-inspection result, distinct from BVL’s datatype. -/
@[hol "cakeml/compiler/backend/semantics/bviSemScript.sml" "dest_thunk_ret"]
inductive DestThunkResult where
  | badRef
  | notThunk
  | isThunk : ThunkMode → Value → DestThunkResult

private def toBroad (refs : HolFiniteMapExact Nat (Ref Value)) : Nat → Option (Ref Value) := refs.lookup
private def ofBroad (lookup : Nat → Option (Ref Value))
    (support : ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact Nat (Ref Value) := ⟨lookup, support⟩

/-- Lookup and finite-support roundtrip for the canonical thunk store. -/
theorem holFmapAsFiniteSupportParamWitness_destThunk_refs
    (refs : HolFiniteMapExact Nat (Ref Value)) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs := by
  cases refs
  exact ⟨rfl, rfl, rfl⟩

/-- Inspect a BVI value as a thunk pointer with the source error cases. -/
@[hol "cakeml/compiler/backend/semantics/bviSemScript.sml" "dest_thunk_def"
  (fmap_as_finite_support_parameters := [refs])]
def destThunk (value : Value) (refs : HolFiniteMapExact Nat (Ref Value)) : DestThunkResult :=
  match value with
  | .refPtr flag index => match refs.lookup index with
    | none => .badRef
    | some (.thunk mode v) => if flag then .badRef else .isThunk mode v
    | some _ => .notThunk
  | _ => .notThunk

/-- Translate the distinct BVL thunk-result constructors into BVI's. -/
def fromBvlThunkResult : BvlSem.DestThunkResult → DestThunkResult
  | .badRef => .badRef
  | .notThunk => .notThunk
  | .isThunk mode value => .isThunk mode value

/-- Both original thunk inspections agree after translating their distinct
result constructors. This is Flapjack infrastructure for pass simulation. -/
theorem destThunk_fromBvl (value : Value) (refs : HolFiniteMapExact Nat (Ref Value)) :
    destThunk value refs = fromBvlThunkResult (BvlSem.destThunk value refs) := by
  cases value <;> try rfl
  case refPtr flag index =>
    cases found : refs.lookup index with
    | none => simp [destThunk, BvlSem.destThunk, found, fromBvlThunkResult]
    | some entry =>
      cases entry <;> simp [destThunk, BvlSem.destThunk, found, fromBvlThunkResult]
      case thunk mode value => cases flag <;> rfl

end Flapjack.Compiler.Backend.BviSem
