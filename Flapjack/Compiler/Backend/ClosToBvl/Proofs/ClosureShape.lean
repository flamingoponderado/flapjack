module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ClosureArguments
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ClosureRelation
public import Flapjack.FiniteMap.BroadCodec

@[expose] public section

/-! Source and target shapes implied by the closure relation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- The canonical reference-map parameter roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_clRel_dest_refs
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad refs)).lookup key = refs.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad refs)).finiteSupport = refs.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad refs) = refs := by
  cases refs
  exact ⟨rfl, rfl, rfl⟩

/-- Related closures have no saved arguments and a target closure block. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "cl_rel_dest"
  (fmap_as_finite_support_parameters := [refs])]
theorem clRel_dest (maxApp : Nat) (fs : Nat → Prop)
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (code : Spt (Nat × Bvl.Exp))
    (cl : ClosSem.Value) (target : BvlSem.Value) (env : List ClosSem.Value) (values : List BvlSem.Value)
    (related : clRel maxApp fs refs code (env, values) cl target) :
    getOldArgs cl = some [] ∧
      ∃ location arity fields, target = .block 30 (.codePtr location :: .number (Int.ofNat arity) :: fields) := by
  cases related with
  | closure bound positive loc vars compiled installed lookup =>
    exact ⟨rfl, _, _, _, rfl⟩
  | singletonRec bound positive loc vars compiled installed lookup =>
    exact ⟨rfl, _, _, _, rfl⟩
  | @mutualRec exps expsPs ps rs loc r env ys k expsEq psEq positions valuesEq fresh stored length index locs vars installed =>
    have bound : k < expsPs.length := by simpa [expsEq] using index
    subst rs
    rw [Flapjack.holEl_eq_getElem _ _ (by simpa using bound)]
    simp only [List.getElem_map]
    cases entry : expsPs[k] with
    | mk pair ptr =>
      cases pair with
      | mk arity expression =>
        exact ⟨rfl, ptr, arity - 1, [.refPtr true r], rfl⟩

end Flapjack.Compiler.Backend.ClosToBvl
