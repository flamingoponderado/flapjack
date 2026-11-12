module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateRelation

@[expose] public section

/-! Preservation of closure, value and environment relations as stores grow. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- The unmapped-reference frame also composes across sequential evaluations. -/
theorem unmappedRefsSubmap_trans
    {refs1 refs2 refs3 : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)}
    {f1 f2 f3 : HolFiniteMapExact Nat Nat}
    (first : unmappedRefsSubmap refs1 refs2 f1 f2)
    (second : unmappedRefsSubmap refs2 refs3 f2 f3) :
    unmappedRefsSubmap refs1 refs3 f1 f3 := by
  intro key value found fresh
  obtain ⟨intermediate, stillFresh⟩ := first key value found fresh
  exact second key value intermediate stillFresh

/-- Preserving the unprotected references and keeping them unprotected
preserves a closure relation. This general frame lemma supports simulations
across changes to the store and protected set. -/
theorem clRel_grow_refs {maxApp : Nat} {fs1 fs2 : Nat → Prop}
    {refs1 refs2 : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)}
    {code : Spt (Nat × Bvl.Exp)} {env cl target}
    (related : clRel maxApp fs1 refs1 code env cl target)
    (frame : ∀ p cell, refs1.lookup p = some cell → ¬ fs1 p →
      refs2.lookup p = some cell ∧ ¬ fs2 p) :
    clRel maxApp fs2 refs2 code env cl target := by
  cases related with
  | closure bound positive loc vars compiled installed lookup =>
      exact .closure bound positive loc vars compiled installed lookup
  | singletonRec bound positive loc vars compiled installed lookup =>
      exact .singletonRec bound positive loc vars compiled installed lookup
  | mutualRec exps ps positions values fresh stored length index loc vars installed =>
      obtain ⟨stored', fresh'⟩ := frame _ _ stored fresh
      exact .mutualRec exps ps positions values fresh' stored' length index loc vars installed

namespace FreshProtectedRefHOL

/-- The target reference map uses its canonical finite-support carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_BvlSem.State {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness

/-- Adding a fresh reference address to the protected set preserves closure relations. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "cl_rel_NEW_F"
  (fmap_as_finite_support_relation := [BvlSem.State.refs])]
theorem clRel_newProtected {C F : Type} (maxApp : Nat) (fs : Nat → Prop)
    (t : BvlSem.State C F) (env : List ClosSem.Value) (ys : List BvlSem.Value) (qq : Nat) :
    ∀ x y, clRel maxApp fs t.refs t.code (env, ys) x y → t.refs.lookup qq = none →
      clRel maxApp (fun p => p = qq ∨ fs p) t.refs t.code (env, ys) x y := by
  intro x y related fresh
  apply clRel_grow_refs related
  intro p cell found outside
  have different : p ≠ qq := by
    intro equal
    subst p
    rw [fresh] at found
    contradiction
  exact ⟨found, by simp [different, outside]⟩

end FreshProtectedRefHOL

/-- Growing the relocation map and preserving unmapped references preserves
related values. This candidate is not tagged as the HOL lemma until its
finite-map representation and inferred source type are reviewed. -/
theorem vRel_grow_refs {maxApp : Nat} {f1 f2 : HolFiniteMapExact Nat Nat}
    {refs1 refs2 : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)}
    {code : Spt (Nat × Bvl.Exp)} {x y}
    (related : vRel maxApp f1 refs1 code x y)
    (submap : f1.submap f2) (frame : unmappedRefsSubmap refs1 refs2 f1 f2) :
    vRel maxApp f2 refs2 code x y := by
  refine vRel.rec
    (motive_1 := fun x y _ => vRel maxApp f2 refs2 code x y)
    (motive_2 := fun xs ys _ => List.Forall₂ (vRel maxApp f2 refs2 code) xs ys)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ related
  · intro n
    exact .number n
  · intro w
    exact .word64 w
  · intro tag xs ys related ih
    exact .block ih
  · intro bs p lookup fresh
    obtain ⟨lookup', fresh'⟩ := frame p _ lookup fresh
    exact .byteVector lookup' fresh'
  · intro b r1 r2 lookup
    exact .refPtr (submap r1 r2 lookup)
  · intro env fvs cl p n ys envRel closure ih
    exact .closure ih (clRel_grow_refs closure frame)
  · intro env fvs argEnv ys numArgs cl clApp cl' envRel argRel nonempty bound lookup added arity closure
      envIh argIh
    exact .partialClosure envIh argIh nonempty bound lookup added arity
      (clRel_grow_refs closure frame)
  · exact .nil
  · intro a b xs ys head tail headIh tailIh
    exact .cons headIh tailIh

/-- Related environments remain related under the same store growth. This is
Flapjack infrastructure until the source relation's carrier review is complete. -/
theorem envRel_grow_refs {maxApp : Nat} {f1 f2 : HolFiniteMapExact Nat Nat}
    {refs1 refs2 : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)}
    {code : Spt (Nat × Bvl.Exp)} {env targetEnv}
    (related : envRel maxApp f1 refs1 code env targetEnv)
    (submap : f1.submap f2) (frame : unmappedRefsSubmap refs1 refs2 f1 f2) :
    envRel maxApp f2 refs2 code env targetEnv := by
  induction env generalizing targetEnv with
  | nil => trivial
  | cons head tail ih =>
      cases targetEnv with
      | nil => exact False.elim related
      | cons targetHead targetTail =>
          exact ⟨vRel_grow_refs related.1 submap frame, ih related.2⟩

/-- Extending the target store at a fresh address preserves related environments. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "env_rel_NEW_REF"
  (fmap_as_finite_support_relation := [f, refs])]
theorem envRel_newRef (maxApp : Nat) (f : HolFiniteMapExact Nat Nat)
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (code : Spt (Nat × Bvl.Exp))
    (r : Nat) (cell : BvlSem.Ref BvlSem.Value) :
    ∀ x y, envRel maxApp f refs code x y ∧ refs.lookup r = none →
      envRel maxApp f (refs.updateEq (r, cell)) code x y := by
  intro x y ⟨related, fresh⟩
  apply envRel_grow_refs related
  · intro key value found
    exact found
  · intro key value found outside
    have different : key ≠ r := by
      intro eq
      subst key
      rw [fresh] at found
      contradiction
    exact ⟨by simpa [HolFiniteMapExact.lookup_updateEq,
      Flapjack.FUPDATE_HOL, different] using found, outside⟩

/-- Sequential evaluation can grow the relocation map, references, and code
together while preserving a value relation. -/
theorem vRel_grow {maxApp : Nat} {f1 f2 : HolFiniteMapExact Nat Nat}
    {refs1 refs2 : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)}
    {code1 code2 : Spt (Nat × Bvl.Exp)} {x y}
    (related : vRel maxApp f1 refs1 code1 x y)
    (submap : f1.submap f2) (frame : unmappedRefsSubmap refs1 refs2 f1 f2)
    (codeGrowth : sptSubspt code1 code2) : vRel maxApp f2 refs2 code2 x y :=
  vRel_subspt f2 refs2 ⟨vRel_grow_refs related submap frame, codeGrowth⟩

/-- The analogous combined growth property for environments. -/
theorem envRel_grow {maxApp : Nat} {f1 f2 : HolFiniteMapExact Nat Nat}
    {refs1 refs2 : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)}
    {code1 code2 : Spt (Nat × Bvl.Exp)} {env targetEnv}
    (related : envRel maxApp f1 refs1 code1 env targetEnv)
    (submap : f1.submap f2) (frame : unmappedRefsSubmap refs1 refs2 f1 f2)
    (codeGrowth : sptSubspt code1 code2) : envRel maxApp f2 refs2 code2 env targetEnv :=
  envRel_subspt _ f2 refs2 _ _ _ (envRel_grow_refs related submap frame) _ codeGrowth

end Flapjack.Compiler.Backend.ClosToBvl
