import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Equality

/-! General equality correspondence for closure-to-BVL values. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Related source and target values have the same equality result. This
candidate is untagged pending source evaluator and carrier review. -/
theorem doEq_related {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (states : stateRel f s t)
    (a b : ClosSem.Value) (x y : BvlSem.Value)
    (first : vRel s.maxApp f t.refs t.code a x) (second : vRel s.maxApp f t.refs t.code b y) :
    ClosSem.doEq a b = BvlSem.doEq t.refs x y := by
  by_cases different : sourceEqClass a ≠ sourceEqClass b
  · exact doEq_class_mismatch a b x y first second different
  · by_cases closureA : sourceIsClosure a
    · by_cases closureB : sourceIsClosure b
      · exact doEq_related_closures a b x y first second closureA closureB
      · exact doEq_closure_nonClosure a b x y first second closureA closureB
    · by_cases closureB : sourceIsClosure b
      · exact doEq_nonClosure_closure a b x y first second closureA closureB
      · cases a <;> cases b <;> simp_all [sourceEqClass, sourceIsClosure]
        case number.number left right =>
          have hx := vRel_number_inv first
          have hy := vRel_number_inv second
          subst x; subst y
          simp [ClosSem.doEq, BvlSem.doEq]
        case word64.word64 left right =>
          have hx := vRel_word64_inv first
          have hy := vRel_word64_inv second
          subst x; subst y
          simp [ClosSem.doEq, BvlSem.doEq]
        case byteVector.byteVector left right =>
          exact doEq_related_byteVectors left right x y first second
        case byteVector.refPtr left flag ptr =>
          exact doEq_byteVector_refPtr s t states left flag ptr x y first second
        case refPtr.byteVector flag ptr right =>
          exact doEq_refPtr_byteVector s t states flag ptr right x y first second
        case refPtr.refPtr flagA ptrA flagB ptrB =>
          exact doEq_related_refPtrs s t states flagA flagB ptrA ptrB x y first second
        case block.block tagA xs tagB ys =>
          obtain ⟨xs', rfl, relA⟩ := vRel_block_inv first
          obtain ⟨ys', rfl, relB⟩ := vRel_block_inv second
          have fieldsEq : ClosSem.doEqList xs ys = BvlSem.doEqList t.refs xs' ys' := by
            have worker : ∀ {as_ : List ClosSem.Value} {as' : List BvlSem.Value},
                List.Forall₂ (vRel s.maxApp f t.refs t.code) as_ as' →
                (∀ v ∈ as_, v ∈ xs) →
                ∀ {bs : List ClosSem.Value} {bs' : List BvlSem.Value},
                List.Forall₂ (vRel s.maxApp f t.refs t.code) bs bs' →
                ClosSem.doEqList as_ bs = BvlSem.doEqList t.refs as' bs' := by
              intro as_ as' rel membership
              induction rel with
              | nil =>
                intro bs bs' relB
                cases relB <;> simp [ClosSem.doEqList, BvlSem.doEqList]
              | @cons left targetLeft rest targetRest head tail ih =>
                intro bs bs' relB
                cases relB with
                | nil => simp [ClosSem.doEqList, BvlSem.doEqList]
                | @cons right targetRight restRight targetRestRight headB tailB =>
                  have member : left ∈ xs := membership left (by simp)
                  have one := doEq_related s t states left right targetLeft targetRight head headB
                  simp only [ClosSem.doEqList, BvlSem.doEqList, ← one]
                  cases ClosSem.doEq left right with
                  | typeError => rfl
                  | val flag =>
                    cases flag with
                    | false => rfl
                    | true =>
                      apply ih
                      · intro v hv
                        exact membership v (by simp [hv])
                      · exact tailB
            exact worker relA (by intro v h; exact h) relB
          exact doEq_related_blocks tagA tagB xs ys xs' ys' relA relB fieldsEq
termination_by sizeOf a
decreasing_by
  subst a
  simp_wf
  have bound := List.sizeOf_lt_of_mem member
  omega

/-- Successful equality dispatch returns related Boolean values and does not
change either state. -/
theorem blockEqual_dispatch {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (args : List ClosSem.Value) (targets : List BvlSem.Value)
    (s next : ClosSem.State C F) (t : BvlSem.State C F)
    (states : stateRel f s t)
    (related : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targets)
    (value : ClosSem.Value)
    (run : ClosSem.doApp (.blockOp .equal) args s = .val (value, next)) :
    ∃ targetValue, BvlSem.doApp (.blockOp .equal) targets t = .val (targetValue, t) ∧
      next = s ∧ vRel s.maxApp f t.refs t.code value targetValue := by
  cases args with
  | nil => simp [ClosSem.doApp, ClosSem.applyBlock] at run
  | cons a rest =>
    cases rest with
    | nil => simp [ClosSem.doApp, ClosSem.applyBlock] at run
    | cons b rest =>
      cases rest with
      | nil =>
        cases related with
        | cons first tail =>
          cases tail with
          | cons second tail =>
            cases tail
            have same := doEq_related s t states a b _ _ first second
            cases result : ClosSem.doEq a b with
            | typeError => simp [ClosSem.doApp, ClosSem.applyBlock, result] at run
            | val flag =>
              have targetResult := same.symm.trans result
              simp [ClosSem.doApp, ClosSem.applyBlock, result] at run
              rcases run with ⟨rfl, rfl⟩
              refine ⟨BvlSem.boolValue flag, ?_, rfl, vRel_bool flag⟩
              simp [BvlSem.doApp, BvlSem.applyBlock, targetResult]
      | cons c rest => simp [ClosSem.doApp, ClosSem.applyBlock] at run

end Flapjack.Compiler.Backend.ClosToBvl
