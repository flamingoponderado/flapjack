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

/-- Canonical reference-map codec for the arity theorem. -/
theorem holFmapAsFiniteSupportParamWitness_clRel_getNumArgs_refs
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad refs)).lookup key = refs.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad refs)).finiteSupport = refs.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad refs) = refs :=
  holFmapAsFiniteSupportParamWitness_clRel_dest_refs refs key

/-- The target's stored arity determines the source closure's full arity. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "cl_rel_get_num_args"
  (fmap_as_finite_support_parameters := [refs])]
theorem clRel_getNumArgs (maxApp : Nat) (fs : Nat → Prop)
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (code : Spt (Nat × Bvl.Exp))
    (env : List ClosSem.Value) (ys : List BvlSem.Value) (func : ClosSem.Value)
    (tag : Nat) (p : BvlSem.Value) (totalArgs : Nat) (fvs : List BvlSem.Value)
    (related : clRel maxApp fs refs code (env, ys) func
      (.block tag (p :: .number (Int.ofNat totalArgs - 1) :: fvs))) :
    getNumArgs func = some totalArgs := by
  generalize targetEq : BvlSem.Value.block tag (p :: .number (Int.ofNat totalArgs - 1) :: fvs) = target at related
  cases related with
  | closure bound positive loc vars compiled installed lookup =>
    simp [getNumArgs] at *
    omega
  | singletonRec bound positive loc vars compiled installed lookup =>
    simp [getNumArgs, Flapjack.holEl, Flapjack.holHd] at *
    omega
  | @mutualRec exps entries ps rs loc r env ys k expsEq psEq positions valuesEq fresh stored length index locs vars installed =>
    have bound : k < entries.length := by simpa [expsEq] using index
    subst rs
    subst exps
    rw [Flapjack.holEl_eq_getElem _ _ (by simpa using bound)] at targetEq
    simp only [List.getElem_map] at targetEq
    cases entry : entries[k] with
    | mk pair address =>
      cases pair with
      | mk arity body =>
        have member : ((arity, body), address) ∈ entries := by
          rw [← entry]
          exact List.getElem_mem bound
        have positive : arity ≠ 0 := (installed _ member).2.1
        simp [entry] at targetEq
        simp only [getNumArgs, Option.some.injEq]
        rw [Flapjack.holEl_eq_getElem k _ (by simpa using bound)]
        simp only [List.getElem_map, entry]
        omega

/-- Canonical reference-map codec for the location theorem. -/
theorem holFmapAsFiniteSupportParamWitness_clRel_getLoc_refs
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad refs)).lookup key = refs.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad refs)).finiteSupport = refs.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad refs) = refs :=
  holFmapAsFiniteSupportParamWitness_clRel_dest_refs refs key

/-- The target code pointer recovers the source closure location. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "cl_rel_get_loc"
  (fmap_as_finite_support_parameters := [refs])]
theorem clRel_getLoc (maxApp : Nat) (fs : Nat → Prop)
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (code : Spt (Nat × Bvl.Exp))
    (env : List ClosSem.Value) (values : List BvlSem.Value) (func : ClosSem.Value)
    (tag p : Nat) (n : BvlSem.Value) (ys : List BvlSem.Value)
    (related : clRel maxApp fs refs code (env, values) func
      (.block tag (.codePtr p :: n :: ys))) :
    numStubs maxApp ≤ p ∧ getLoc func = some (p - numStubs maxApp) := by
  generalize targetEq : BvlSem.Value.block tag (.codePtr p :: n :: ys) = target at related
  cases related with
  | closure bound positive loc vars compiled installed lookup =>
    simp [getLoc] at *
    omega
  | singletonRec bound positive loc vars compiled installed lookup =>
    simp [getLoc] at *
    omega
  | @mutualRec exps entries ps rs loc r env ys k expsEq psEq positions valuesEq fresh stored length index locs vars installed =>
    have bound : k < entries.length := by simpa [expsEq] using index
    have entryAddress : (entries[k]'bound).2 = loc + numStubs maxApp + 2 * k := by
      have actual : ps[k]? = some (entries[k]'bound).2 := by
        simp [psEq, List.getElem?_map, List.getElem?_eq_getElem bound]
      have expected : ps[k]? = some (loc + numStubs maxApp + 2 * k) := by
        simp [positions, bound]
      exact Option.some.inj (actual.symm.trans expected)
    subst rs
    rw [Flapjack.holEl_eq_getElem _ _ (by simpa using bound)] at targetEq
    simp only [List.getElem_map] at targetEq
    cases entry : entries[k] with
    | mk pair address =>
      cases pair with
      | mk arity body =>
        simp [entry] at targetEq entryAddress
        simp [getLoc]
        omega

end Flapjack.Compiler.Backend.ClosToBvl
