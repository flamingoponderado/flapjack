import Flapjack.Compiler.Backend.BviTmc.Proofs.ValueRelation
import Flapjack.Compiler.Backend.Semantics.BviSem.State
import Flapjack.SemanticPrimitivesProps.ResultRelation

/-! Exception, return and optimized-result relations for TMC simulation. -/
namespace Flapjack.Compiler.Backend.BviTmc.ResultRelation
open BviSem BvlSem SemanticPrimitivesHOL SemanticPrimitivesProps

private def maptoBroadlookup (f : HolFiniteMapExact Nat Nat) : Nat → Option Nat := f.lookup
private def mapofBroad (lookup : Nat → Option Nat)
    (support : ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact Nat Nat :=
  ⟨lookup, support⟩

theorem holFmapAsFiniteSupportParamWitness_eorRel_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- Exceptions relate their payloads, and returns relate their value lists. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "eor_rel_def"
  (fmap_as_finite_support_parameters := [f])]
def eorRel (f : HolFiniteMapExact Nat Nat) : ExnOrRet → ExnOrRet → Prop
  | .exn a, .exn b => valueRel f a b
  | .ret a, .ret b => List.Forall₂ (valueRel f) a b
  | _, _ => False

theorem holFmapAsFiniteSupportParamWitness_optResRel_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- Optimized workers return the unit block on success and related errors otherwise. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "opt_res_rel_def"
  (fmap_as_finite_support_parameters := [f])]
def optResRel (f : HolFiniteMapExact Nat Nat) : BviResult → BviResult → Prop
  | .val _, .val [.block 0 []] => True
  | .err a, .err b => excRel (eorRel f) a b
  | _, _ => False

/-- Flapjack infrastructure: exception and return relations survive map extension. -/
theorem eorRel_submap (f g : HolFiniteMapExact Nat Nat) (a b : ExnOrRet)
    (related : eorRel f a b) (submap : finiteSubmap f g) : eorRel g a b := by
  cases a <;> cases b <;> simp only [eorRel] at related ⊢
  · exact valueRel_submap f g _ _ related submap
  · exact listRel_submap f g _ _ related submap

/-- Flapjack infrastructure: optimized results survive map extension. -/
theorem optResRel_submap (f g : HolFiniteMapExact Nat Nat) (a b : BviResult)
    (related : optResRel f a b) (submap : finiteSubmap f g) : optResRel g a b := by
  cases a with
  | val values =>
    cases b with
    | val values' =>
      cases values' with
      | nil => exact related
      | cons value rest =>
        cases value with
        | block tag fields =>
          cases rest <;> cases tag <;> cases fields <;> simp_all [optResRel]
        | _ => cases rest <;> simp_all [optResRel]
    | err error => exact related.elim
  | err error =>
    cases b with
    | val values => exact related.elim
    | err error' =>
      exact excRel_mono (eorRel f) (eorRel g) (fun a b h => eorRel_submap f g a b h submap) _ _ related

end Flapjack.Compiler.Backend.BviTmc.ResultRelation
