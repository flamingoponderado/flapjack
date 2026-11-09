import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateRelation

/-! Preservation of closure, value and environment relations as stores grow. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Relocation-map extension composes across sequential evaluations. -/
theorem relocationSubmap_trans {f1 f2 f3 : HolFiniteMapExact Nat Nat}
    (first : relocationSubmap f1 f2) (second : relocationSubmap f2 f3) :
    relocationSubmap f1 f3 := by
  intro key value found
  exact second key value (first key value found)

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

/-- Extending the protected set and preserving the unprotected part of the
reference store preserves a closure relation. This candidate remains untagged
pending review of its finite-map carriers against the original local lemma. -/
theorem clRel_grow_refs {maxApp : Nat} {fs1 fs2 : Nat → Prop}
    {refs1 refs2 : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)}
    {code : Spt (Nat × Bvl.Exp)} {env cl target}
    (related : clRel maxApp fs1 refs1 code env cl target)
    (_subset : ∀ p, fs1 p → fs2 p)
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

/-- Growing the relocation map and preserving unmapped references preserves
related values. This candidate is not tagged as the HOL lemma until its
finite-map representation and inferred source type are reviewed. -/
theorem vRel_grow_refs {maxApp : Nat} {f1 f2 : HolFiniteMapExact Nat Nat}
    {refs1 refs2 : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)}
    {code : Spt (Nat × Bvl.Exp)} {x y}
    (related : vRel maxApp f1 refs1 code x y)
    (submap : relocationSubmap f1 f2) (frame : unmappedRefsSubmap refs1 refs2 f1 f2) :
    vRel maxApp f2 refs2 code x y := by
  have rangeSubset : ∀ p, (∃ n, f1.lookup n = some p) → ∃ n, f2.lookup n = some p := by
    intro p ⟨n, lookup⟩
    exact ⟨n, submap n p lookup⟩
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
    exact .closure ih (clRel_grow_refs closure rangeSubset frame)
  · intro env fvs argEnv ys numArgs cl clApp cl' envRel argRel nonempty bound lookup added arity closure
      envIh argIh
    exact .partialClosure envIh argIh nonempty bound lookup added arity
      (clRel_grow_refs closure rangeSubset frame)
  · exact .nil
  · intro a b xs ys head tail headIh tailIh
    exact .cons headIh tailIh

/-- Related environments remain related under the same store growth. This is
Flapjack infrastructure until the source relation's carrier review is complete. -/
theorem envRel_grow_refs {maxApp : Nat} {f1 f2 : HolFiniteMapExact Nat Nat}
    {refs1 refs2 : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)}
    {code : Spt (Nat × Bvl.Exp)} {env targetEnv}
    (related : envRel maxApp f1 refs1 code env targetEnv)
    (submap : relocationSubmap f1 f2) (frame : unmappedRefsSubmap refs1 refs2 f1 f2) :
    envRel maxApp f2 refs2 code env targetEnv := by
  induction env generalizing targetEnv with
  | nil => trivial
  | cons head tail ih =>
      cases targetEnv with
      | nil => exact False.elim related
      | cons targetHead targetTail =>
          exact ⟨vRel_grow_refs related.1 submap frame, ih related.2⟩

/-- Sequential evaluation can grow the relocation map, references, and code
together while preserving a value relation. -/
theorem vRel_grow {maxApp : Nat} {f1 f2 : HolFiniteMapExact Nat Nat}
    {refs1 refs2 : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)}
    {code1 code2 : Spt (Nat × Bvl.Exp)} {x y}
    (related : vRel maxApp f1 refs1 code1 x y)
    (submap : relocationSubmap f1 f2) (frame : unmappedRefsSubmap refs1 refs2 f1 f2)
    (codeGrowth : sptSubspt code1 code2) : vRel maxApp f2 refs2 code2 x y :=
  vRel_subspt f2 refs2 (vRel_grow_refs related submap frame) codeGrowth

/-- The analogous combined growth property for environments. -/
theorem envRel_grow {maxApp : Nat} {f1 f2 : HolFiniteMapExact Nat Nat}
    {refs1 refs2 : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)}
    {code1 code2 : Spt (Nat × Bvl.Exp)} {env targetEnv}
    (related : envRel maxApp f1 refs1 code1 env targetEnv)
    (submap : relocationSubmap f1 f2) (frame : unmappedRefsSubmap refs1 refs2 f1 f2)
    (codeGrowth : sptSubspt code1 code2) : envRel maxApp f2 refs2 code2 env targetEnv :=
  envRel_subspt f2 refs2 (envRel_grow_refs related submap frame) codeGrowth

end Flapjack.Compiler.Backend.ClosToBvl
