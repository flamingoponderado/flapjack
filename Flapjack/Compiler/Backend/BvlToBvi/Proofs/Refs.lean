import Flapjack.Compiler.Backend.BvlToBvi.Proofs.Values
import Flapjack.Compiler.Backend.Semantics.BviSem.State

/-! Reference-store component of the BVL-to-BVI state relation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value Ref)

private def toBroad (refs : HolFiniteMapExact Nat (Ref Value)) : Nat → Option (Ref Value) := refs.lookup
private def ofBroad (lookup : Nat → Option (Ref Value))
    (support : ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact Nat (Ref Value) := ⟨lookup, support⟩

/-- Canonical reference-map lookup and support roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_bvOk_refs
    (refs : HolFiniteMapExact Nat (Ref Value)) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs := by
  cases refs
  exact ⟨rfl, rfl, rfl⟩

mutual
/-- All reference pointers in a value belong to the given reference domain.
`bvOkList_iff` relates the local recursion to the source's `EVERY` clause. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "bv_ok_def"
  (fmap_as_finite_support_parameters := [refs])]
def bvOk (refs : HolFiniteMapExact Nat (Ref Value)) : Value → Prop
  | .refPtr _ address => refs.lookup address ≠ none
  | .block _ values => bvOkList refs values
  | _ => True
termination_by value => sizeOf value

/-- Flapjack's list traversal for the source `EVERY (bv_ok refs)` clause. -/
def bvOkList (refs : HolFiniteMapExact Nat (Ref Value)) : List Value → Prop
  | [] => True
  | value :: values => bvOk refs value ∧ bvOkList refs values
termination_by values => sizeOf values
end

/-- The helper traverses exactly the values named by the source `EVERY`. -/
theorem bvOkList_iff (refs : HolFiniteMapExact Nat (Ref Value)) (values : List Value) :
    bvOkList refs values ↔ ∀ value ∈ values, bvOk refs value := by
  induction values with
  | nil => simp [bvOkList]
  | cons value values ih => simp [bvOkList, ih]

/-- The unit value contains no reference pointer. This is Flapjack's local
consequence of `bvOk`; the HOL theorem remains untagged here. -/
theorem bvOk_unit (refs : HolFiniteMapExact Nat (Ref Value)) :
    bvOk refs Flapjack.Compiler.Backend.BvlSem.unitValue := by
  simp [Flapjack.Compiler.Backend.BvlSem.unitValue, bvOk, bvOkList]

/-- The reference-cell case split used by the source state relation. This is
Flapjack infrastructure: the original relation inlines the case split. -/
def adjustRef (relocate : Nat → Nat) : Ref Value → Ref Value
  | .valueArray values => .valueArray (values.map (adjustBv relocate))
  | .thunk mode value => .thunk mode (adjustBv relocate value)
  | other => other

/-- The exact reference-domain injection and lookup clauses from the source
state relation. This extracted component is not the full HOL state relation. -/
def refsRel (relocate : Nat → Nat) (source target : HolFiniteMapExact Nat (Ref Value)) : Prop :=
  (∀ key, source.lookup key ≠ none → target.lookup (relocate key) ≠ none) ∧
  (∀ left right, source.lookup left ≠ none → source.lookup right ≠ none →
    relocate left = relocate right → left = right) ∧
  ∀ key value, source.lookup key = some value →
    target.lookup (relocate key) = some (adjustRef relocate value)

/-- Related value arrays contain relocated values. -/
theorem refsRel_valueArray {relocate : Nat → Nat} {source target : HolFiniteMapExact Nat (Ref Value)}
    (related : refsRel relocate source target) {key : Nat} {values : List Value}
    (lookup : source.lookup key = some (.valueArray values)) :
    target.lookup (relocate key) = some (.valueArray (values.map (adjustBv relocate))) := by
  simpa [adjustRef] using related.2.2 key (.valueArray values) lookup

/-- Related byte arrays are unchanged. -/
theorem refsRel_byteArray {relocate : Nat → Nat} {source target : HolFiniteMapExact Nat (Ref Value)}
    (related : refsRel relocate source target) {key : Nat} {mutableRef : Bool} {bytes : List (BitVec 8)}
    (lookup : source.lookup key = some (.byteArray mutableRef bytes)) :
    target.lookup (relocate key) = some (.byteArray mutableRef bytes) := by
  simpa [adjustRef] using related.2.2 key (.byteArray mutableRef bytes) lookup

/-- Related thunks relocate their contained value. -/
theorem refsRel_thunk {relocate : Nat → Nat} {source target : HolFiniteMapExact Nat (Ref Value)}
    (related : refsRel relocate source target) {key : Nat} {mode : AstHOL.ThunkMode} {value : Value}
    (lookup : source.lookup key = some (.thunk mode value)) :
    target.lookup (relocate key) = some (.thunk mode (adjustBv relocate value)) := by
  simpa [adjustRef] using related.2.2 key (.thunk mode value) lookup

/-- The source relation leaves mutable-block cells unchanged. -/
theorem refsRel_mutBlock {relocate : Nat → Nat} {source target : HolFiniteMapExact Nat (Ref Value)}
    (related : refsRel relocate source target) {key tag : Nat} {flag : Bool}
    {before after : List Value} {value : Value}
    (lookup : source.lookup key = some (.mutBlock tag flag before value after)) :
    target.lookup (relocate key) = some (.mutBlock tag flag before value after) := by
  simpa [adjustRef] using related.2.2 key (.mutBlock tag flag before value after) lookup

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
