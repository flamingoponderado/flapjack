module

public import Flapjack.Compiler.Backend.BviTmc.Proofs.ValueRelation
public import Flapjack.Compiler.Backend.Semantics.BviSem.State
public import Flapjack.SemanticPrimitivesProps.ResultRelation

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Exception, return and optimized-result relations for TMC simulation. -/
namespace Flapjack.Compiler.Backend.BviTmc.ResultRelation
open BviSem BvlSem SemanticPrimitivesHOL SemanticPrimitivesProps

private def maptoBroadlookup (f : HolFiniteMapExact Nat Nat) : Nat → Option Nat := f.lookup
private def mapofBroad (lookup : Nat → Option Nat)
    (support : ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact Nat Nat :=
  ⟨lookup, support⟩

theorem holFmapAsFiniteSupportParamWitness_eorRel_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- Exceptions relate their payloads, and returns relate their value lists.

Intended HOL counterpart, pending statement and finite-map carrier source review.
Former reference: @[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "eor_rel_def" (fmap_as_finite_support_parameters := [f])] -/
def eorRel (f : HolFiniteMapExact Nat Nat) : ExnOrRet → ExnOrRet → Prop
  | .exn a, .exn b => valueRel f a b
  | .ret a, .ret b => List.Forall₂ (valueRel f) a b
  | _, _ => False

theorem holFmapAsFiniteSupportParamWitness_optResRel_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- Optimized workers return the unit block on success and related errors otherwise.

Intended HOL counterpart, pending statement and finite-map carrier source review.
Former reference: @[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "opt_res_rel_def" (fmap_as_finite_support_parameters := [f])] -/
def optResRel (f : HolFiniteMapExact Nat Nat) : BviResult → BviResult → Prop
  | .val _, .val [.block 0 []] => True
  | .err a, .err b => excRel (eorRel f) a b
  | _, _ => False

end Flapjack.Compiler.Backend.BviTmc.ResultRelation
