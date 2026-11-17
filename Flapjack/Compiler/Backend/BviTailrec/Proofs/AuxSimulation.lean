module

public import Flapjack.Compiler.Backend.BviTailrec.Proofs.CodeRelation
public import Flapjack.Compiler.Backend.Semantics.BviSem.ApplyRuntimeFrame
public import Flapjack.Misc.Option.Rel

@[expose] public section

namespace Flapjack.Compiler.Backend.BviTailrec
open BvlSem

namespace AuxSimulationCarrier
/-- The BVI reference-map carrier roundtrips through its finite-support view. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviSem.BviState C F, BviSem.BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end AuxSimulationCarrier

/-- Related states agree with the source runtime frame. This Flapjack helper
connects the state relation to the shared dispatcher-frame infrastructure. -/
private theorem relatedRuntimeFrame {C F : Type} (source : BviSem.BviState (Nat × C) F)
    (target : BviSem.BviState C F) (related : stateRel source target) :
    BviSem.runtimeFrame source target = target := by
  cases source
  cases target
  simp_all [stateRel, BviSem.runtimeFrame]

/-- A source transition preserving compiler fields transports the relation to
its runtime frame. This Flapjack helper supports the full auxiliary theorem. -/
private theorem relatedNextRuntimeFrame {C F : Type} (source next : BviSem.BviState (Nat × C) F)
    (target : BviSem.BviState C F) (related : stateRel source target)
    (fields : next.compile = source.compile ∧ next.compileOracle = source.compileOracle ∧
      next.code = source.code) :
    stateRel next (BviSem.runtimeFrame next target) := by
  obtain ⟨compilerEq, oracleEq, codeEq⟩ := fields
  obtain ⟨refs, clock, global, ffi, oracle, compiler, code, names, condition, bound⟩ := related
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [BviSem.runtimeFrame, oracleEq] using oracle
  · simpa [BviSem.runtimeFrame, compilerEq] using compiler
  · simpa [BviSem.runtimeFrame, codeEq] using code
  · simpa [BviSem.runtimeFrame, codeEq] using names
  · simpa [BviSem.runtimeFrame, oracleEq] using condition
  · simpa [BviSem.runtimeFrame, oracleEq] using bound

/-- The BVI auxiliary dispatcher preserves the nested result and state relation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "state_rel_do_app_aux"
  (fmap_as_finite_support := [refs])]
theorem stateRel_doAppAux {C F : Type} (op : ClosLang.Op) (vs : List Value)
    (source : BviSem.BviState (Nat × C) F)
    (result : Option (Option (Value × BviSem.BviState (Nat × C) F)))
    (target : BviSem.BviState C F)
    (premises : BviSem.doAppAux op vs source = result ∧ stateRel source target ∧
      op ≠ .install ∧ ∀ n, op ≠ .label n) :
    ∃ targetResult : Option (Option (Value × BviSem.BviState C F)),
      BviSem.doAppAux op vs target = targetResult ∧
      optionRel (optionRel (fun a b => a.1 = b.1 ∧ stateRel a.2 b.2)) result targetResult := by
  obtain ⟨run, related, _, notLabel⟩ := premises
  have frame := BviSem.doAppAux_frame op vs source target (Or.inr notLabel)
  rw [relatedRuntimeFrame source target related, run] at frame
  refine ⟨_, frame, ?_⟩
  cases result with
  | none => simp [optionRel]
  | some inner =>
    cases inner with
    | none => simp [optionRel]
    | some pair =>
      obtain ⟨value, next⟩ := pair
      have fields := BviSem.doAppAux_compiler_fields op vs source next value run
      exact ⟨rfl, relatedNextRuntimeFrame source next target related fields⟩

/-- Successful non-install, non-label dispatch preserves the state relation.
The full dispatcher inherits the real-model assumption in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "state_rel_do_app"
  (fmap_as_finite_support := [refs])]
theorem stateRel_doApp {C F : Type} (op : ClosLang.Op) (vs : List Value)
    (source : BviSem.BviState (Nat × C) F) (result : Value)
    (sourceNext : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F)
    (premises : BviSem.doApp op vs source = .val (result, sourceNext) ∧
      stateRel source target ∧ op ≠ .install ∧ ∀ n, op ≠ .label n) :
    ∃ targetNext : BviSem.BviState C F,
      BviSem.doApp op vs target = .val (result, targetNext) ∧ stateRel sourceNext targetNext := by
  obtain ⟨run, related, notInstall, notLabel⟩ := premises
  have nonInstall (state : BviSem.BviState (Nat × C) F) :
      BviSem.doApp op vs state = BviSem.doAppFallback op vs state := by
    cases op <;> simp_all [BviSem.doApp]
  have nonInstallTarget (state : BviSem.BviState C F) :
      BviSem.doApp op vs state = BviSem.doAppFallback op vs state := by
    cases op <;> simp_all [BviSem.doApp]
  rw [nonInstall source] at run
  rw [nonInstallTarget target]
  obtain ⟨targetResult, targetAux, relation⟩ := stateRel_doAppAux op vs source
    (BviSem.doAppAux op vs source) target ⟨rfl, related, notInstall, notLabel⟩
  cases aux : BviSem.doAppAux op vs source with
  | none => simp [BviSem.doAppFallback, aux] at run
  | some inner =>
    cases inner with
    | some pair =>
      obtain ⟨value, next⟩ := pair
      simp [BviSem.doAppFallback, aux] at run
      obtain ⟨rfl, rfl⟩ := run
      rw [aux] at relation
      cases targetResult with
      | none => contradiction
      | some targetInner =>
        cases targetInner with
        | none => contradiction
        | some targetPair =>
          obtain ⟨targetValue, targetNext⟩ := targetPair
          simp only [optionRel] at relation
          obtain ⟨rfl, relatedNext⟩ := relation
          exact ⟨targetNext, by simp [BviSem.doAppFallback, targetAux], relatedNext⟩
    | none =>
      rw [aux] at relation
      cases targetResult with
      | none => contradiction
      | some targetInner =>
        cases targetInner with
        | some pair => contradiction
        | none =>
          simp only [BviSem.doAppFallback, aux] at run
          cases bvlRun : BvlSem.doApp op vs (BviSem.toBvl source) with
          | err error => cases error <;> simp [bvlRun] at run
          | val pair =>
            obtain ⟨value, nextBvl⟩ := pair
            simp only [bvlRun, SemanticPrimitivesHOL.Result.val.injEq, Prod.mk.injEq] at run
            obtain ⟨rfl, rfl⟩ := run
            have notGlobal : ∀ operation, op ≠ .globOp operation := by
              intro operation eq
              subst op
              exact BviSem.doAppAux_delegates_not_global operation vs source aux
            have domain : ∀ key, sptDomain (BviSem.toBvl source).code key →
                sptDomain (BviSem.toBvl target).code key := by
              intro key present
              rw [BviSem.toBvl_domain] at present ⊢
              exact codeRel_domain source.code target.code (stateRel_codeRel source target related) key present
            have swapped := BvlProps.doAppFallbackRvalSwap op vs (BviSem.toBvl source) nextBvl value
              (BviSem.toBvl target) notGlobal ⟨bvlRun, notInstall, domain⟩
            have bvlFrame : BvlProps.fallbackFrame (BviSem.toBvl source) (BviSem.toBvl target) =
                BviSem.toBvl target := by
              have eq := BviSem.toBvl_runtimeFrame source target
              simpa only [relatedRuntimeFrame source target related] using eq.symm
            rw [bvlFrame] at swapped
            have fromFrame := BviSem.fromBvl_runtimeFrame nextBvl (BviSem.toBvl target) source target
            rw [relatedRuntimeFrame source target related] at fromFrame
            refine ⟨BviSem.runtimeFrame (BviSem.fromBvl nextBvl source) target, ?_, ?_⟩
            · simp only [BviSem.doAppFallback, targetAux, swapped]
              rw [fromFrame]
            · exact relatedNextRuntimeFrame source (BviSem.fromBvl nextBvl source) target related
                ⟨rfl, rfl, rfl⟩

/-- Non-install, non-label, non-build dispatcher errors are preserved between
related states. The full dispatcher inherits the real-model assumption in
SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "state_rel_do_app_err"
  (fmap_as_finite_support := [refs])]
theorem stateRel_doAppErr {C F : Type} (op : ClosLang.Op) (vs : List Value)
    (source : BviSem.BviState (Nat × C) F)
    (error : SemanticPrimitivesHOL.ErrorResult BviSem.ExnOrRet)
    (target : BviSem.BviState C F)
    (premises : BviSem.doApp op vs source = .err error ∧ stateRel source target ∧
      op ≠ .install ∧ (∀ n, op ≠ .label n) ∧
      (∀ parts : List ClosLang.ConstPart, op ≠ .blockOp (.build parts))) :
    BviSem.doApp op vs target = .err error := by
  obtain ⟨run, related, notInstall, notLabel, _⟩ := premises
  have nonInstall (state : BviSem.BviState (Nat × C) F) :
      BviSem.doApp op vs state = BviSem.doAppFallback op vs state := by
    cases op <;> simp_all [BviSem.doApp]
  have nonInstallTarget (state : BviSem.BviState C F) :
      BviSem.doApp op vs state = BviSem.doAppFallback op vs state := by
    cases op <;> simp_all [BviSem.doApp]
  rw [nonInstall source] at run
  rw [nonInstallTarget target]
  obtain ⟨targetResult, targetAux, relation⟩ := stateRel_doAppAux op vs source
    (BviSem.doAppAux op vs source) target ⟨rfl, related, notInstall, notLabel⟩
  cases aux : BviSem.doAppAux op vs source with
  | none =>
    rw [aux] at relation
    cases targetResult with
    | none => simpa [BviSem.doAppFallback, aux, targetAux] using run
    | some inner => contradiction
  | some inner =>
    cases inner with
    | some pair => simp [BviSem.doAppFallback, aux] at run
    | none =>
      rw [aux] at relation
      cases targetResult with
      | none => contradiction
      | some targetInner =>
        cases targetInner with
        | some pair => contradiction
        | none =>
          simp only [BviSem.doAppFallback, aux] at run
          cases bvlRun : BvlSem.doApp op vs (BviSem.toBvl source) with
          | val pair =>
            cases pair
            simp [bvlRun] at run
          | err bvlError =>
            have notGlobal : ∀ operation, op ≠ .globOp operation := by
              intro operation eq
              subst op
              exact BviSem.doAppAux_delegates_not_global operation vs source aux
            have swapped := BvlProps.doAppFallbackRerrSwap op vs (BviSem.toBvl source) bvlError
              (BviSem.toBvl target) notGlobal ⟨bvlRun, notInstall, Or.inr notLabel⟩
            have bvlFrame : BvlProps.fallbackFrame (BviSem.toBvl source) (BviSem.toBvl target) =
                BviSem.toBvl target := by
              have eq := BviSem.toBvl_runtimeFrame source target
              simpa only [relatedRuntimeFrame source target related] using eq.symm
            rw [bvlFrame] at swapped
            cases bvlError <;> simp_all [BviSem.doAppFallback]

end Flapjack.Compiler.Backend.BviTailrec
