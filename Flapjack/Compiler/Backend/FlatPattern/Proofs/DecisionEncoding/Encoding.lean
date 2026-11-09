import Flapjack.Compiler.Backend.PatternSemantics.Semantics
import Flapjack.Compiler.Backend.FlatPattern.Proofs.NaiveMatch
import Flapjack.HolArb

/-! Flat-pattern value and reference encoding. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (storeLookup)

mutual
/-- Project flat values into the pattern compiler's abstract value domain.
The stamp case is `Option.map Prod.fst`, and the recursive field traversal
implements HOL's map by `encodeValues_eq_map`. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "encode_val_def"]
def encodeValue : FlatSem.Value → PatternSemantics.Term
  | .litv lit => .litv lit
  | .conv stamp values => .term (stamp.map Prod.fst) (encodeValues values)
  | .loc _ index => .refPtr index
  | _ => .other
termination_by value => sizeOf value

/-- Encode constructor fields in their original order. -/
def encodeValues : List FlatSem.Value → List PatternSemantics.Term
  | [] => []
  | value :: values => encodeValue value :: encodeValues values
termination_by values => sizeOf values
end

/-- The auxiliary list traversal agrees with mapping the value encoding. -/
theorem encodeValues_eq_map (values : List FlatSem.Value) : encodeValues values = values.map encodeValue := by
  induction values with
  | nil => simp [encodeValues]
  | cons value values ih => simp [encodeValues, ih]

/-- A finite map containing exactly the reference-valued entries of a flat
store. The map's support is bounded by the source store length. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "encode_refs_def"
  (fmap_as_finite_support_result)]
def encodeRefs {C F : Type} (state : FlatSem.State C F) : HolFiniteMapExact Nat PatternSemantics.Term where
  lookup index := match storeLookup index state.refs with
    | some (.refv value) => some (encodeValue value)
    | _ => none
  finiteSupport := by
    refine ⟨List.range state.refs.length, ?_⟩
    intro index present
    apply List.mem_range.mpr
    by_cases inside : index < state.refs.length
    · exact inside
    · have absent : storeLookup index state.refs = none := by
        apply List.getElem?_eq_none_iff.mpr
        omega
      simp [absent] at present

/-- HOL-shaped FUN_FMAP lookup: its domain contains bounded reference entries,
and its value function retains HOL's arbitrary non-reference fallback. -/
noncomputable def encodeRefsRaw {C F : Type} (state : FlatSem.State C F) (index : Nat) : Option PatternSemantics.Term := by
  classical
  let _ : Nonempty FlatSem.Value := ⟨.conv none []⟩
  exact if index < state.refs.length ∧ ∃ value, state.refs[index]? = some (.refv value) then
    some (encodeValue (match state.refs[index]? with
      | some (.refv value) => value
      | _ => Flapjack.holArb FlatSem.Value))
  else none

/-- The finite-support map has the same reference-store lookup as the raw map. -/
theorem holFmapAsFiniteSupportResultWitness_encodeRefs {C F : Type}
    (state : FlatSem.State C F) (index : Nat) :
    (encodeRefs state).lookup index = encodeRefsRaw state index := by
  classical
  cases found : state.refs[index]? with
  | none => simp [encodeRefs, encodeRefsRaw, storeLookup, found]
  | some entry =>
    have bound : index < state.refs.length := (List.getElem?_eq_some_iff.mp found).1
    change (match state.refs[index]? with
      | some (.refv value) => some (encodeValue value)
      | _ => none) = _
    unfold encodeRefsRaw
    rw [found]
    cases entry <;> simp [bound]

end Flapjack.Compiler.Backend.FlatPattern
