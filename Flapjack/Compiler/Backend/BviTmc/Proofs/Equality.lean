import Flapjack.Compiler.Backend.BviTmc.Proofs.HeapRelation
import Flapjack.Compiler.Backend.Semantics.BvlSem.Equality

/-! Structural equality under the TMC pointer and heap relations. -/
namespace Flapjack.Compiler.Backend.BviTmc
open BvlSem

/-- Equality of two related reference pointers is preserved by the related
heaps and injective pointer map. -/
private theorem doEq_refPtr (f : HolFiniteMapExact Nat Nat)
    (refs target : HolFiniteMapExact Nat (Ref Value)) (a b : Bool) (n m n' m' : Nat)
    (left : f.lookup n = some m) (right : f.lookup n' = some m')
    (heaps : stateRefRel f refs target) (injective : fmapInj f) :
    doEq refs (.refPtr a n) (.refPtr b n') = doEq target (.refPtr a m) (.refPtr b m') := by
  obtain ⟨v, w, sourceLeft, targetLeft, relLeft⟩ := stateRefRel_lookup f n m refs target left heaps
  obtain ⟨v', w', sourceRight, targetRight, relRight⟩ := stateRefRel_lookup f n' m' refs target right heaps
  have addressEq : (m = m') ↔ (n = n') := fmapInj_lookup_eq f n m n' m' injective left right
  cases relLeft <;> cases relRight <;> cases a <;> cases b <;>
    simp [doEq, sourceLeft, sourceRight, targetLeft, targetRight, addressEq]
  all_goals split <;> simp_all

mutual
/-- Equality of related values is unchanged by pointer relocation. -/
private theorem doEq_rel (f : HolFiniteMapExact Nat Nat) (refs target : HolFiniteMapExact Nat (Ref Value))
    (x1 x2 y1 y2 : Value) (first : valueRel f x1 y1) (second : valueRel f x2 y2)
    (heaps : stateRefRel f refs target) (injective : fmapInj f) :
    doEq refs x1 x2 = doEq target y1 y2 := by
  cases first with
  | number a => cases second <;> simp [doEq]
  | word64 a => cases second <;> simp [doEq]
  | codePtr a => cases second <;> simp [doEq]
  | refPtr n m b lookup =>
    cases second with
    | refPtr n' m' b' lookup' => exact doEq_refPtr f refs target b b' n m n' m' lookup lookup' heaps injective
    | _ => simp [doEq]
  | block tag xs ys pairs =>
    cases second with
    | block tag' xs' ys' pairs' =>
      have len : xs.length = ys.length := pairs.length_eq
      have len' : xs'.length = ys'.length := pairs'.length_eq
      have closure : isClosure tag xs ↔ isClosure tag ys := by
        simp only [isClosure]
        have empty : xs = [] ↔ ys = [] := by
          constructor <;> intro h <;> simp_all
        simp [empty]
      have closure' : isClosure tag' xs' ↔ isClosure tag' ys' := by
        simp only [isClosure]
        have empty : xs' = [] ↔ ys' = [] := by
          constructor <;> intro h <;> simp_all
        simp [empty]
      rw [doEq.eq_def, doEq.eq_def]
      dsimp only
      rw [propext closure, propext closure']
      simp only [len, len']
      split <;> rename_i firstCondition
      · split <;> rfl
      · split
        · exact doEqList_rel f refs target xs xs' ys ys' pairs pairs' heaps injective
        · rfl
    | _ => simp [doEq]
termination_by sizeOf x1

/-- List equality is unchanged for lists of related values. -/
private theorem doEqList_rel (f : HolFiniteMapExact Nat Nat) (refs target : HolFiniteMapExact Nat (Ref Value))
    (x1 x2 y1 y2 : List Value) (first : List.Forall₂ (valueRel f) x1 y1)
    (second : List.Forall₂ (valueRel f) x2 y2) (heaps : stateRefRel f refs target) (injective : fmapInj f) :
    doEqList refs x1 x2 = doEqList target y1 y2 := by
  cases first with
  | nil => cases second <;> simp [doEqList]
  | cons head tail =>
    cases second with
    | nil => simp [doEqList]
    | cons head' tail' =>
      simp only [doEqList]
      rw [doEq_rel f refs target _ _ _ _ head head' heaps injective]
      cases h : doEq target _ _ with
      | typeError => rfl
      | val b => cases b <;> simp [doEqList_rel f refs target _ _ _ _ tail tail' heaps injective]
termination_by sizeOf x1
end

/-- Related values and heaps produce the same structural equality result,
both for single values and for value lists. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_eq_v_rel"
  (fmap_as_finite_support_relation := [f, refs, target])]
theorem doEq_value_rel (f : HolFiniteMapExact Nat Nat) :
    (∀ (refs : HolFiniteMapExact Nat (Ref Value)) x1 x2 (target : HolFiniteMapExact Nat (Ref Value)) y1 y2,
      valueRel f x1 y1 → valueRel f x2 y2 → stateRefRel f refs target → fmapInj f →
        doEq refs x1 x2 = doEq target y1 y2) ∧
    (∀ (refs : HolFiniteMapExact Nat (Ref Value)) x1s x2s (target : HolFiniteMapExact Nat (Ref Value)) y1s y2s,
      List.Forall₂ (valueRel f) x1s y1s → List.Forall₂ (valueRel f) x2s y2s →
        stateRefRel f refs target → fmapInj f → doEqList refs x1s x2s = doEqList target y1s y2s) := by
  exact ⟨fun refs x1 x2 target y1 y2 first second heaps injective =>
      doEq_rel f refs target x1 x2 y1 y2 first second heaps injective,
    fun refs x1 x2 target y1 y2 first second heaps injective =>
      doEqList_rel f refs target x1 x2 y1 y2 first second heaps injective⟩

end Flapjack.Compiler.Backend.BviTmc
