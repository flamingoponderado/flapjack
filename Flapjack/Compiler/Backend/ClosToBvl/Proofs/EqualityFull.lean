module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Equality

@[expose] public section

/-! General equality correspondence for closure-to-BVL values. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Scalar equality correspondence under the source map conditions. -/
private theorem doEqCore {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (injective : ∀ a b y, f.lookup a = some y → f.lookup b = some y → a = b)
    (noFrozen : ∀ a y bytes, f.lookup a = some y → refs.lookup y ≠ some (.byteArray true bytes))
    (a b : ClosSem.Value) (x y : BvlSem.Value)
    (first : vRel maxApp f refs code a x) (second : vRel maxApp f refs code b y) :
    ClosSem.doEq a b = BvlSem.doEq refs x y := by
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
          exact doEq_byteVector_refPtr noFrozen left flag ptr x y first second
        case refPtr.byteVector flag ptr right =>
          exact doEq_refPtr_byteVector noFrozen flag ptr right x y first second
        case refPtr.refPtr flagA ptrA flagB ptrB =>
          exact doEq_related_refPtrs injective noFrozen flagA flagB ptrA ptrB x y first second
        case block.block tagA xs tagB ys =>
          obtain ⟨xs', rfl, relA⟩ := vRel_block_inv first
          obtain ⟨ys', rfl, relB⟩ := vRel_block_inv second
          have fieldsEq : ClosSem.doEqList xs ys = BvlSem.doEqList refs xs' ys' := by
            have worker : ∀ {as_ : List ClosSem.Value} {as' : List BvlSem.Value},
                List.Forall₂ (vRel maxApp f refs code) as_ as' →
                (∀ v ∈ as_, v ∈ xs) →
                ∀ {bs : List ClosSem.Value} {bs' : List BvlSem.Value},
                List.Forall₂ (vRel maxApp f refs code) bs bs' →
                ClosSem.doEqList as_ bs = BvlSem.doEqList refs as' bs' := by
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
                  have one := doEqCore injective noFrozen left right targetLeft targetRight head headB
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

/-- Canonical pointer-map codec for equality correspondence. -/
theorem holFmapAsFiniteSupportParamWitness_doEqCorrespondence_f
    (f : HolFiniteMapExact Nat Nat) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).lookup key = f.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).finiteSupport = f.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f) = f :=
  holFmapAsFiniteSupportParamWitness_vRel_f f key

/-- Canonical target-reference codec for equality correspondence. -/
theorem holFmapAsFiniteSupportParamWitness_doEqCorrespondence_refs
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad refs)).lookup key = refs.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad refs)).finiteSupport = refs.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad refs) = refs :=
  holFmapAsFiniteSupportParamWitness_vRel_refs refs key

/-- Related scalar values and value lists give the same equality results. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "do_eq"
  (fmap_as_finite_support_parameters := [f, refs])]
theorem doEqCorrespondence (maxApp : Nat) (f : HolFiniteMapExact Nat Nat)
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (code : Spt (Nat × Bvl.Exp))
    (premises : (∀ a b y, f.lookup a = some y → f.lookup b = some y → a = b) ∧
      (∀ a y bytes, f.lookup a = some y → refs.lookup y ≠ some (.byteArray true bytes))) :
    (∀ a b x y, vRel maxApp f refs code a x ∧ vRel maxApp f refs code b y →
      ClosSem.doEq a b = BvlSem.doEq refs x y) ∧
    (∀ as_ bs xs ys, List.Forall₂ (vRel maxApp f refs code) as_ xs ∧
      List.Forall₂ (vRel maxApp f refs code) bs ys →
      ClosSem.doEqList as_ bs = BvlSem.doEqList refs xs ys) := by
  obtain ⟨injective, noFrozen⟩ := premises
  constructor
  · intro a b x y related
    exact doEqCore injective noFrozen a b x y related.1 related.2
  · intro as_ bs xs ys related
    obtain ⟨first, second⟩ := related
    induction first generalizing bs ys with
    | nil => cases second <;> simp [ClosSem.doEqList, BvlSem.doEqList]
    | @cons a x rest tail head first ih =>
      cases second with
      | nil => simp [ClosSem.doEqList, BvlSem.doEqList]
      | @cons b y more targetMore head2 second =>
        have same := doEqCore injective noFrozen a b x y head head2
        simp only [ClosSem.doEqList, BvlSem.doEqList, ← same]
        cases ClosSem.doEq a b with
        | typeError => rfl
        | val flag => cases flag with
          | false => rfl
          | true => exact ih _ _ second

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
            have same := (doEqCorrespondence s.maxApp f t.refs t.code ⟨states.2.2.2.1, states.2.2.2.2.1⟩).1 a b _ _ ⟨first, second⟩
            cases result : ClosSem.doEq a b with
            | typeError => simp [ClosSem.doApp, ClosSem.applyBlock, result] at run
            | val flag =>
              have targetResult := same.symm.trans result
              simp [ClosSem.doApp, ClosSem.applyBlock, result] at run
              rcases run with ⟨rfl, rfl⟩
              refine ⟨BvlSem.boolValue flag, ?_, rfl, (vRel_bool_iff _ _ _ _ flag (.number 0) _).1.mpr rfl⟩
              simp [BvlSem.doApp, BvlSem.applyBlock, targetResult]
      | cons c rest => simp [ClosSem.doApp, ClosSem.applyBlock] at run

end Flapjack.Compiler.Backend.ClosToBvl
