import Flapjack.Compiler.Backend.BviTmc.Proofs.FinaliseHoles
import Flapjack.Compiler.Backend.BviTmc.Proofs.MutableBlockOld
import Flapjack.Compiler.Backend.Semantics.BviSem.Finalise

/-! Finalisation of a related mutable-constructor chain. -/
namespace Flapjack.Compiler.Backend.BviTmc.FinaliseRelation
open BviTmc BviSem BvlSem CallBlockEnvironment FinaliseHoles

private theorem valueRel_finalise (f : HolFiniteMapExact Nat Nat)
    (sourceHeap targetHeap : HolFiniteMapExact Nat (Ref Value)) (source target : Value)
    (heaps : stateRefRel f sourceHeap targetHeap) (values : valueRel f source target) :
    finaliseCons target targetHeap = some (target, targetHeap) := by
  cases values with
  | number i => rw [finaliseCons.eq_def]
  | word64 w => rw [finaliseCons.eq_def]
  | block tag xs ys related => rw [finaliseCons.eq_def]
  | codePtr n => rw [finaliseCons.eq_def]
  | refPtr n m flag mapped =>
    obtain ⟨_, _, _, targetFound, cells⟩ := stateRefRel_lookup f n m sourceHeap targetHeap mapped heaps
    cases cells <;> rw [finaliseCons.eq_def] <;> dsimp only <;> rw [targetFound]

/-- Flapjack infrastructure: finalising a related mutable chain produces a
related immutable value and preserves the heap invariants. It remains
untagged pending source review of the recursive finalisation carrier. -/
theorem evaluate_finalise_cons (v2 : Value) (targetRefs : HolFiniteMapExact Nat (Ref Value))
    (f : HolFiniteMapExact Nat Nat) (fNext : HolFiniteMapExact Nat Nat)
    (sourceRefs : HolFiniteMapExact Nat (Ref Value)) (v1 : Value) (oldRefs : HolFiniteMapExact Nat (Ref Value))
    (heaps : stateRefRel fNext sourceRefs targetRefs) (blocks : mutableBlockRel fNext oldRefs targetRefs v1 v2)
    (still : holesStillNotFinalised f oldRefs targetRefs) :
    ∃ (v3 : Value) (resultRefs : HolFiniteMapExact Nat (Ref Value)),
      finaliseCons v2 targetRefs = some (v3, resultRefs) ∧ valueRel fNext v1 v3 ∧
      stateRefRel fNext sourceRefs resultRefs ∧ holesUnchangedExcept fNext targetRefs resultRefs ∅ ∧
      holesStillNotFinalised f oldRefs resultRefs := by
  classical
  have plain (v1 v2 : Value) (values : valueRel fNext v1 v2) :
      ∃ (v3 : Value) (resultRefs : HolFiniteMapExact Nat (Ref Value)),
        finaliseCons v2 targetRefs = some (v3, resultRefs) ∧ valueRel fNext v1 v3 ∧
        stateRefRel fNext sourceRefs resultRefs ∧ holesUnchangedExcept fNext targetRefs resultRefs ∅ ∧
        holesStillNotFinalised f oldRefs resultRefs :=
    ⟨v2, targetRefs, valueRel_finalise fNext sourceRefs targetRefs v1 v2 heaps values, values,
      heaps, holesUnchanged_refl fNext targetRefs ∅, still⟩
  cases v1 with
  | block sourceTag fields =>
    cases v2 with
    | refPtr flag ptr =>
      by_cases invalid : flag = true ∨ ptr ∈ mapRange fNext ∨ ptr ∈ oldRefs.domain
      · rw [mutableBlockRel.eq_def] at blocks
        simp [invalid] at blocks
      · have flagFalse : flag = false := by cases flag <;> simp_all
        have outside : ptr ∉ mapRange fNext := fun h => invalid (Or.inr (Or.inl h))
        have absent : ptr ∉ oldRefs.domain := fun h => invalid (Or.inr (Or.inr h))
        rw [mutableBlockRel.eq_def] at blocks
        simp only [invalid, if_false] at blocks
        cases found : targetRefs.lookup ptr with
        | none => rw [found] at blocks; contradiction
        | some cell =>
          cases cell with
          | mutBlock tag finalised left child right =>
            rw [found] at blocks
            obtain ⟨tagEq, finalEq, sourceLeft, sourceChild, sourceRight, shape, leftRel, inner, rightRel⟩ := blocks
            subst finalised
            have eraseEq : (@HolFiniteMapExact.eraseEq Nat (Ref Value) (Classical.decEq Nat) targetRefs ptr) =
                targetRefs.eraseEq ptr := by
              apply HolFiniteMapExact.ext_lookup
              intro k
              by_cases equal : k = ptr <;> simp [HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL, equal]
            have stillErased : holesStillNotFinalised f oldRefs (targetRefs.eraseEq ptr) := by
              rw [← eraseEq]
              exact holesStill_sub ptr oldRefs f targetRefs absent still
            obtain ⟨childValue, childRefs, childRun, childRelated, childHeaps, childUnchanged, childStill⟩ :=
              evaluate_finalise_cons child (targetRefs.eraseEq ptr) f fNext sourceRefs sourceChild oldRefs
                (stateRefRel_sub ptr fNext sourceRefs targetRefs outside heaps) inner
                stillErased
            have listRel : List.Forall₂ (valueRel fNext) (sourceLeft ++ [sourceChild] ++ sourceRight)
                (left ++ [childValue] ++ right) := by
              have appendRel : ∀ {a b c d : List Value}, List.Forall₂ (valueRel fNext) a b →
                  List.Forall₂ (valueRel fNext) c d → List.Forall₂ (valueRel fNext) (a ++ c) (b ++ d) := by
                intro a b c d first second
                induction first with
                | nil => exact second
                | cons head tail ih => exact .cons head ih
              simpa [List.append_assoc] using appendRel leftRel (.cons childRelated rightRel)
            refine ⟨.block tag (left ++ [childValue] ++ right),
              childRefs.updateEq (ptr, .mutBlock tag true left child right), ?_, ?_, ?_, ?_, ?_⟩
            · subst flag
              rw [finaliseCons.eq_def]
              dsimp only
              rw [found]
              simp [childRun]
            · subst sourceTag
              rw [shape]
              exact .block _ _ _ listRel
            · exact stateRefRel_filled fNext sourceRefs childRefs ptr _ childHeaps (fun i mapped => outside ⟨i, mapped⟩)
            · have childUnchanged' : holesUnchangedExcept fNext
                  (@HolFiniteMapExact.eraseEq Nat (Ref Value) (Classical.decEq Nat) targetRefs ptr) childRefs ∅ := by
                rw [eraseEq]
                exact childUnchanged
              have updateEq : (@HolFiniteMapExact.updateEq Nat (Ref Value) (Classical.decEq Nat) childRefs
                  (ptr, .mutBlock tag true left child right)) = childRefs.updateEq (ptr, .mutBlock tag true left child right) := by
                apply HolFiniteMapExact.ext_lookup
                intro k
                by_cases equal : k = ptr <;> simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, equal]
              rw [← updateEq]
              exact holesUnchanged_finalised fNext () ptr targetRefs childRefs tag false left child right true
                childUnchanged' found outside
            · have updateEq : (@HolFiniteMapExact.updateEq Nat (Ref Value) (Classical.decEq Nat) childRefs
                  (ptr, .mutBlock tag true left child right)) = childRefs.updateEq (ptr, .mutBlock tag true left child right) := by
                apply HolFiniteMapExact.ext_lookup
                intro k
                by_cases equal : k = ptr <;> simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, equal]
              rw [← updateEq]
              exact holesStill_non_dom f oldRefs childRefs ptr tag left child right childStill absent
          | _ => rw [found] at blocks; contradiction
    | _ => rw [mutableBlockRel.eq_def] at blocks; exact plain _ _ blocks
  | _ => cases v2 <;> rw [mutableBlockRel.eq_def] at blocks <;> exact plain _ _ blocks
termination_by targetRefs.card
decreasing_by
  apply BviSem.card_eraseEq_lt
  simp [found]

end Flapjack.Compiler.Backend.BviTmc.FinaliseRelation
