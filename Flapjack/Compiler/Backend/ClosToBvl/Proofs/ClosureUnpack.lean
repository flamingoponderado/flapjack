module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.RemainingArgs
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.GenericPartial

@[expose] public section

/-! Unpacking related source and target closures. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

namespace ClosureUnpackCarrier

/-- Canonical roundtrip for the target state's reference-map field. -/
theorem holFmapAsFiniteSupportRelationWitness_BvlSem.State {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness

/-- Canonical codec roundtrip for the explicit reference correspondence map. -/
theorem holFmapAsFiniteSupportParamWitness_unpackClosureThm_f
    (f : HolFiniteMapExact Nat Nat) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).lookup key = f.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).finiteSupport = f.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f) = f :=
  holFmapAsFiniteSupportParamWitness_vRelNumRemArgs_f f key

end ClosureUnpackCarrier

/-- A related target closure unpacks to its original closure and saved arguments. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "unpack_closure_thm"
  (fmap_as_finite_support_relation := [BvlSem.State.refs, f])]
theorem unpackClosureThm {C F : Type} (maxApp : Nat) (f : HolFiniteMapExact Nat Nat)
    (t : BvlSem.State C F) (source : ClosSem.Value) (tag : Nat) (ptr : BvlSem.Value)
    (n : Nat) (rest : List BvlSem.Value)
    (premises : vRel maxApp f t.refs t.code source
        (.block tag (ptr :: .number (Int.ofNat n - 1) :: rest)) ∧
      numRemainingArgs source = some n) :
    ∃ prev total clo,
      UnpackClosure (.block tag (ptr :: .number (Int.ofNat n - 1) :: rest)) (prev, total, clo) ∧
      total < maxApp ∧ n = total - prev.length + 1 ∧
      (tag = BackendCommon.closureTag → prev = [] ∧
        clo = .block tag (ptr :: .number (Int.ofNat n - 1) :: rest)) := by
  rcases premises with ⟨related, remaining⟩
  obtain ⟨_, _, _, _, _, positive, _⟩ := vRelNumRemArgs f t.refs t.code source
    (.block tag (ptr :: .number (Int.ofNat n - 1) :: rest)) n maxApp ⟨related, remaining⟩
  generalize eq : BvlSem.Value.block tag (ptr :: .number (Int.ofNat n - 1) :: rest) = target at related
  cases related with
  | number | word64 | block | byteVector | refPtr => simp [numRemainingArgs] at remaining
  | @closure env fvs cl p stored ys envRel closure =>
    generalize targetEq : BvlSem.Value.block 30 (.codePtr p :: .number stored :: ys) = target at closure
    cases closure with
    | @closure arity body aux c aux1 loc captured values bound pos locs vars compiled installed lookup =>
      simp only [numRemainingArgs, List.length_nil, Nat.sub_zero, Option.some.injEq] at remaining
      subst n
      refine ⟨[], arity - 1, .block 30 (.codePtr (loc + numStubs maxApp) :: .number (Int.ofNat (arity - 1)) :: fvs), ?_, by omega, ?_, by simp⟩
      · simpa [BackendCommon.closureTag] using
          (UnpackClosure.closure (loc + numStubs maxApp) (Int.ofNat (arity - 1)) fvs (by simp))
      · simp only [List.length_nil, Nat.sub_zero]; omega
    | @singletonRec arity body aux c aux1 loc captured values bound pos locs vars compiled installed lookup =>
      simp [numRemainingArgs, Flapjack.holEl, Flapjack.holHd] at remaining
      subst n
      refine ⟨[], arity - 1, .block 30 (.codePtr (loc + numStubs maxApp) :: .number (Int.ofNat (arity - 1)) :: fvs), ?_, by omega, ?_, by simp⟩
      · simpa [BackendCommon.closureTag] using
          (UnpackClosure.closure (loc + numStubs maxApp) (Int.ofNat (arity - 1)) fvs (by simp))
      · simp only [List.length_nil, Nat.sub_zero]; omega
    | @mutualRec exps entries ps rs loc r captured values k expsEq psEq positions valuesEq fresh stored many index locs vars installed =>
      have selected : exps[k]? = some exps[k] := List.getElem?_eq_getElem index
      cases entry : exps[k] with
      | mk selectedArity selectedBody =>
        have found : exps[k]? = some (selectedArity, selectedBody) := by simpa [entry] using selected
        have relation : clRel maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code (env, fvs)
            (.recclosure (some loc) [] env exps k) (Flapjack.holEl k rs) :=
          .mutualRec expsEq psEq positions valuesEq fresh stored many index locs vars installed
        have ⟨arityBound, arityPositive⟩ := clRel_recclosure_arity relation found
        have nEq : n = selectedArity := by
          simp only [numRemainingArgs, List.length_nil, Nat.sub_zero, Option.some.injEq] at remaining
          rw [Flapjack.holEl_eq_getElem _ _ index, entry] at remaining
          simpa using remaining.symm
        subst n
        obtain ⟨address, payload, targetBody, targetShape, targetLookup⟩ :=
          clRel_recclosure_target_code relation found
        refine ⟨[], selectedArity - 1, Flapjack.holEl k rs, ?_, by omega, ?_, by simp⟩
        · rw [targetShape]
          simpa [BackendCommon.closureTag] using
            (UnpackClosure.closure address (Int.ofNat (selectedArity - 1)) payload (by simp))
        · simp only [List.length_nil, Nat.sub_zero]; omega
  | @partialClosure env fvs saved ys numArgs cl clApp cl' envRel savedRel nonempty bound lookup added arity closure =>
    have empty : getOldArgs cl = some [] := (clRel_dest maxApp _ t.refs t.code cl cl' env fvs closure).1
    have remainingEq : n = numArgs - saved.length := by
      cases cl <;> simp [getOldArgs] at empty <;> simp [addArgs] at added
      all_goals subst source
      all_goals simp [empty, numRemainingArgs, getNumArgs] at remaining arity
      all_goals omega
    have arityBound : numArgs ≤ maxApp := by
      cases closure with
      | closure bound pos loc vars compiled installed lookup =>
        simp [getNumArgs] at arity
        omega
      | singletonRec bound pos loc vars compiled installed lookup =>
        simp [getNumArgs, Flapjack.holEl, Flapjack.holHd] at arity
        omega
      | @mutualRec exps entries ps rs loc r env fvs k expsEq psEq positions valuesEq fresh stored many index locs vars installed =>
        have selected : exps[k]? = some exps[k] := List.getElem?_eq_getElem index
        cases entry : exps[k] with
        | mk selectedArity selectedBody =>
          have found : exps[k]? = some (selectedArity, selectedBody) := by simpa [entry] using selected
          have relation : clRel maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code (env, fvs)
              (.recclosure (some loc) [] env exps k) (Flapjack.holEl k rs) :=
            .mutualRec expsEq psEq positions valuesEq fresh stored many index locs vars installed
          have selectedBound := (clRel_recclosure_arity relation found).1
          simp only [getNumArgs, Option.some.injEq] at arity
          rw [Flapjack.holEl_eq_getElem _ _ index, entry] at arity
          omega
    have savedLen : ys.length = saved.length := savedRel.length_eq.symm
    have savedNonempty : ys ≠ [] := by
      apply List.length_pos_iff.mp
      rw [savedLen]
      exact List.length_pos_iff.mpr nonempty
    have countEq : (numArgs - 1 - saved.length) + ys.length = numArgs - 1 := by omega
    have tagEq : tag = 31 := by
      simp only [BvlSem.Value.block.injEq] at eq
      exact eq.1
    refine ⟨ys, numArgs - 1, cl', ?_, by omega, ?_, ?_⟩
    · have h := UnpackClosure.partialClosure
        (partialAppFnLocation maxApp (numArgs - 1) (ys.length - 1))
        (Int.ofNat (numArgs - 1 - saved.length)) cl' ys savedNonempty (by simp)
      simpa [BackendCommon.partialAppTag, countEq] using h
    · omega
    · simp [tagEq, BackendCommon.closureTag]

end Flapjack.Compiler.Backend.ClosToBvl
