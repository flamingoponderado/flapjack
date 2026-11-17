module

public import Flapjack.Compiler.Backend.BviTmc.Proofs.ValueRelation
public import Flapjack.Compiler.Backend.Semantics.BviSem.State
public import Flapjack.SemanticPrimitivesProps.ResultRelation
public import Flapjack.FiniteMap.BroadCodec

@[expose] public section

/-! Exception, return and optimized-result relations for TMC simulation. -/
namespace Flapjack.Compiler.Backend.BviTmc.ResultRelation
open BviSem BvlSem SemanticPrimitivesHOL SemanticPrimitivesProps

theorem holFmapAsFiniteSupportParamWitness_eorRel_f (f : HolFiniteMapExact Nat Nat) :
    (∀ key, (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).lookup key = f.lookup key) ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).finiteSupport = f.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f) = f := by
  cases f
  exact ⟨fun _ => rfl, rfl, rfl⟩

/-- Exceptions relate their payloads, and returns relate their value lists. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "eor_rel_def"
  (fmap_as_finite_support_parameters := [f])]
def eorRel (f : HolFiniteMapExact Nat Nat) : ExnOrRet → ExnOrRet → Prop
  | .exn a, .exn b => valueRel f a b
  | .ret a, .ret b => List.Forall₂ (valueRel f) a b
  | _, _ => False

theorem holFmapAsFiniteSupportParamWitness_optResRel_f (f : HolFiniteMapExact Nat Nat) :
    (∀ key, (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).lookup key = f.lookup key) ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).finiteSupport = f.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f) = f := by
  cases f
  exact ⟨fun _ => rfl, rfl, rfl⟩

/-- Optimized workers return the unit block on success and related errors otherwise. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "opt_res_rel_def"
  (fmap_as_finite_support_parameters := [f])]
def optResRel (f : HolFiniteMapExact Nat Nat) : BviResult → BviResult → Prop
  | .val _, .val [.block 0 []] => True
  | .err a, .err b => excRel (eorRel f) a b
  | _, _ => False

end Flapjack.Compiler.Backend.BviTmc.ResultRelation
