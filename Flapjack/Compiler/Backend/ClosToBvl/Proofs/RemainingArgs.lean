module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateApp

@[expose] public section

/-! Remaining arities of related source and target closures. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Canonical map witness for the source-to-target reference map. -/
theorem holFmapAsFiniteSupportParamWitness_vRelNumRemArgs_f
    (f : HolFiniteMapExact Nat Nat) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).lookup key = f.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).finiteSupport = f.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f) = f :=
  holFmapAsFiniteSupportParamWitness_vRel_f f key

/-- Canonical map witness for target references. -/
theorem holFmapAsFiniteSupportParamWitness_vRelNumRemArgs_refs
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad refs)).lookup key = refs.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad refs)).finiteSupport = refs.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad refs) = refs :=
  holFmapAsFiniteSupportParamWitness_vRel_refs refs key

/-- A related closure's remaining arity determines its target code entry. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "v_rel_num_rem_args"
  (fmap_as_finite_support_parameters := [f, refs])]
theorem vRelNumRemArgs (f : HolFiniteMapExact Nat Nat)
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (code : Spt (Nat × Bvl.Exp))
    (source : ClosSem.Value) (target : BvlSem.Value) (n maxApp : Nat)
    (premises : vRel maxApp f refs code source target ∧ numRemainingArgs source = some n) :
    ∃ tag ptr rest body, target = .block tag (.codePtr ptr :: .number (Int.ofNat n - 1) :: rest) ∧
      n ≠ 0 ∧ sptLookup ptr code = some (n + 1, body) := by
  rcases premises with ⟨related, remaining⟩
  cases related with
  | number | word64 | block | byteVector | refPtr => simp [numRemainingArgs] at remaining
  | @closure env fvs cl p arity ys envRel closure =>
    generalize targetEq : BvlSem.Value.block 30 (.codePtr p :: .number arity :: ys) = target at closure
    cases closure with
    | @closure arity body aux compiledBody aux1 loc captured values bound positive locs vars compiled installed lookup =>
      simp only [numRemainingArgs, List.length_nil, Nat.sub_zero, Option.some.injEq] at remaining
      subst n
      refine ⟨30, loc + numStubs maxApp, fvs, _, ?_, positive, lookup⟩
      simp [Int.ofNat_sub (by omega : 1 ≤ arity)] at targetEq ⊢
    | @singletonRec arity body aux compiledBody aux1 loc captured values bound positive locs vars compiled installed lookup =>
      simp [numRemainingArgs, Flapjack.holEl, Flapjack.holHd] at remaining
      subst n
      refine ⟨30, loc + numStubs maxApp, fvs, _, ?_, positive, lookup⟩
      simp [Int.ofNat_sub (by omega : 1 ≤ arity)] at targetEq ⊢
    | @mutualRec exps entries ps rs loc r captured values k expsEq psEq positions valuesEq fresh stored many index locs vars installed =>
      have selected : exps[k]? = some exps[k] := List.getElem?_eq_getElem index
      cases entry : exps[k] with
      | mk selectedArity selectedBody =>
        have found : exps[k]? = some (selectedArity, selectedBody) := by simpa [entry] using selected
        have relation : clRel maxApp (fun p => ∃ r, f.lookup r = some p) refs code (env, fvs)
            (.recclosure (some loc) [] env exps k) (Flapjack.holEl k rs) :=
          .mutualRec expsEq psEq positions valuesEq fresh stored many index locs vars installed
        have positive := (clRel_recclosure_arity relation found).2
        have nEq : n = selectedArity := by
          simp only [numRemainingArgs, List.length_nil, Nat.sub_zero, Option.some.injEq] at remaining
          rw [Flapjack.holEl_eq_getElem _ _ index, entry] at remaining
          simpa using remaining.symm
        subst n
        obtain ⟨address, payload, targetBody, targetShape, targetLookup⟩ :=
          clRel_recclosure_target_code relation found
        refine ⟨30, address, payload, targetBody, ?_, positive, targetLookup⟩
        simpa [Int.ofNat_sub (by omega : 1 ≤ selectedArity)] using targetShape
  | @partialClosure env fvs saved ys numArgs cl clApp cl' envRel savedRel nonempty bound lookup added arity closure =>
    have empty : getOldArgs cl = some [] := (clRel_dest maxApp _ refs code cl cl' env fvs closure).1
    have remainingEq : n = numArgs - saved.length := by
      cases cl <;> simp [getOldArgs] at empty <;> simp [addArgs] at added
      all_goals subst source
      all_goals simp [empty, numRemainingArgs, getNumArgs] at remaining arity
      all_goals omega
    have positive : n ≠ 0 := by omega
    have natEq : numArgs - 1 - saved.length = n - 1 := by omega
    have numberEq : Int.ofNat (numArgs - 1 - saved.length) = Int.ofNat n - 1 := by
      rw [natEq]
      simp [Int.ofNat_sub (by omega : 1 ≤ n)]
    refine ⟨31, partialAppFnLocation maxApp (numArgs - 1) (ys.length - 1), cl' :: ys,
      generatePartialAppClosureFn (numArgs - 1) (ys.length - 1), ?_, positive, ?_⟩
    · rw [numberEq]
    · simpa [remainingEq] using lookup

end Flapjack.Compiler.Backend.ClosToBvl
