import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileFfi

/-! Reference-aware equality under BVL-to-BVI relocation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value Ref)

/-- Relocated pointers preserve equality on the allocated source domain. -/
theorem refsRel_addressEq (relocate : Nat → Nat)
    (source target : HolFiniteMapExact Nat (Ref Value)) (left right : Nat)
    (related : refsRel relocate source target) (leftPresent : source.lookup left ≠ none)
    (rightPresent : source.lookup right ≠ none) :
    relocate left = relocate right ↔ left = right := by
  constructor
  · exact related.2.1 left right leftPresent rightPresent
  · intro equal
    rw [equal]

mutual
/-- Equality of well-formed BVL values is invariant under reference relocation.
This is infrastructure for the pass simulation. -/
theorem doEq_relocate (relocate : Nat → Nat)
    (source target : HolFiniteMapExact Nat (Ref Value)) (first second : Value)
    (related : refsRel relocate source target) (firstOk : bvOk source first) (secondOk : bvOk source second) :
    BvlSem.doEq target (adjustBv relocate first) (adjustBv relocate second) = BvlSem.doEq source first second := by
  cases first with
  | number a => cases second <;> simp [adjustBv, BvlSem.doEq]
  | word64 a => cases second <;> simp [adjustBv, BvlSem.doEq]
  | codePtr a => cases second <;> simp [adjustBv, BvlSem.doEq]
  | refPtr flag left =>
    cases second with
    | refPtr flag2 right =>
      have leftPresent : source.lookup left ≠ none := by simpa [bvOk] using firstOk
      have rightPresent : source.lookup right ≠ none := by simpa [bvOk] using secondOk
      cases leftLookup : source.lookup left with
      | none => exact (leftPresent leftLookup).elim
      | some leftCell =>
        cases rightLookup : source.lookup right with
        | none => exact (rightPresent rightLookup).elim
        | some rightCell =>
          have leftTarget := related.2.2 left leftCell leftLookup
          have rightTarget := related.2.2 right rightCell rightLookup
          have addressEq := refsRel_addressEq relocate source target left right related leftPresent rightPresent
          cases flag <;> cases flag2 <;> cases leftCell <;> cases rightCell <;>
            simp [adjustBv, BvlSem.doEq, adjustRef, leftLookup, rightLookup, leftTarget, rightTarget, addressEq]
          all_goals split <;> simp_all
    | _ => simp [adjustBv, BvlSem.doEq]
  | block tag fields =>
    cases second with
    | block tag2 fields2 =>
      have firstFields : bvOkList source fields := by simpa [bvOk] using firstOk
      have secondFields : bvOkList source fields2 := by simpa [bvOk] using secondOk
      have closure1 : BvlSem.isClosure tag (fields.map (adjustBv relocate)) ↔ BvlSem.isClosure tag fields := by
        simp [BvlSem.isClosure]
      have closure2 : BvlSem.isClosure tag2 (fields2.map (adjustBv relocate)) ↔ BvlSem.isClosure tag2 fields2 := by
        simp [BvlSem.isClosure]
      simp only [adjustBv_block, BvlSem.doEq, List.length_map,
        doEqList_relocate relocate source target fields fields2 related firstFields secondFields]
      rw [propext closure1, propext closure2]
    | _ =>
      all_goals simp [adjustBv_block, adjustBv, BvlSem.doEq]
termination_by sizeOf first

/-- List equality commutes with relocation when each value is well formed. -/
theorem doEqList_relocate (relocate : Nat → Nat)
    (source target : HolFiniteMapExact Nat (Ref Value)) (first second : List Value)
    (related : refsRel relocate source target) (firstOk : bvOkList source first) (secondOk : bvOkList source second) :
    BvlSem.doEqList target (first.map (adjustBv relocate)) (second.map (adjustBv relocate)) =
      BvlSem.doEqList source first second := by
  cases first with
  | nil => cases second <;> simp [BvlSem.doEqList]
  | cons head tail =>
    cases second with
    | nil => simp [BvlSem.doEqList]
    | cons head2 tail2 =>
      simp only [bvOkList] at firstOk secondOk
      simp only [List.map_cons, BvlSem.doEqList]
      rw [doEq_relocate relocate source target head head2 related firstOk.1 secondOk.1]
      cases BvlSem.doEq source head head2 with
      | typeError => rfl
      | val b => cases b <;> simp [doEqList_relocate relocate source target tail tail2 related firstOk.2 secondOk.2]
termination_by sizeOf first
end

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
