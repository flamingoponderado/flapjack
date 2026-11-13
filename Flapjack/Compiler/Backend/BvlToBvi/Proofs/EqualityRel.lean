module

public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileFfi

@[expose] public section

/-! Reference-aware equality under BVL-to-BVI relocation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value Ref)

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
          have addressEq : relocate left = relocate right ↔ left = right :=
            ⟨related.2.1 left right leftPresent rightPresent, congrArg relocate⟩
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


namespace DoEqAdjustCarrier
/-- Canonical BVL reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_State {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness

/-- Canonical BVI reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_BviState {C F : Type} :
    (∀ s : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviSem.BviState C F, BviSem.BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end DoEqAdjustCarrier

/-- Successful equality and list equality are preserved by related states. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "do_eq_adjust_lemma"
  (fmap_as_finite_support_relation := [State.refs, BviState.refs, refs])]
theorem doEqAdjustLemma {C F : Type} (r : BvlSem.State (Nat × C) F) (t2 : BviSem.BviState C F)
    (b2 : Nat → Nat) :
    (∀ (refs : HolFiniteMapExact Nat (Ref Value)) (x1 x2 : Value) (b : Bool),
      refs = r.refs ∧ BvlSem.doEq refs x1 x2 = .val b ∧ stateRel b2 r t2 ∧
        bvOk r.refs x1 ∧ bvOk r.refs x2 →
      BvlSem.doEq t2.refs (adjustBv b2 x1) (adjustBv b2 x2) = .val b) ∧
    (∀ (refs : HolFiniteMapExact Nat (Ref Value)) (x1 x2 : List Value) (b : Bool),
      refs = r.refs ∧ BvlSem.doEqList refs x1 x2 = .val b ∧ stateRel b2 r t2 ∧
        x1.Forall (bvOk r.refs) ∧ x2.Forall (bvOk r.refs) →
      BvlSem.doEqList t2.refs (x1.map (adjustBv b2)) (x2.map (adjustBv b2)) = .val b) := by
  constructor
  · intro refs x1 x2 b ⟨refsEq, equal, related, first, second⟩
    subst refs
    rw [doEq_relocate b2 r.refs t2.refs x1 x2 related.1 first second]
    exact equal
  · intro refs x1 x2 b ⟨refsEq, equal, related, first, second⟩
    subst refs
    have firstOk : bvOkList r.refs x1 := (bvOkList_iff _ _).2 (by simpa [List.forall_iff_forall_mem] using first)
    have secondOk : bvOkList r.refs x2 := (bvOkList_iff _ _).2 (by simpa [List.forall_iff_forall_mem] using second)
    rw [doEqList_relocate b2 r.refs t2.refs x1 x2 related.1 firstOk secondOk]
    exact equal

/-- Successful value equality is preserved by related states. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "do_eq_adjust"
  (fmap_as_finite_support_relation := [State.refs, BviState.refs])]
theorem doEqAdjust {C F : Type} (r : BvlSem.State (Nat × C) F) (t2 : BviSem.BviState C F)
    (b2 : Nat → Nat) (x1 x2 : Value) (b : Bool)
    (premises : BvlSem.doEq r.refs x1 x2 = .val b ∧ stateRel b2 r t2 ∧
      bvOk r.refs x1 ∧ bvOk r.refs x2) :
    BvlSem.doEq t2.refs (adjustBv b2 x1) (adjustBv b2 x2) = .val b := by
  exact (doEqAdjustLemma r t2 b2).1 r.refs x1 x2 b ⟨rfl, premises⟩

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
