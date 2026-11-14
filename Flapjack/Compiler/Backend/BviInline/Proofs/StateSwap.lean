module

public import Flapjack.Compiler.Backend.Semantics.BviSem.ApplyRuntimeFrame

@[expose] public section

/-! Source-shaped primitive state-swap lemmas for BVI inlining. -/
namespace Flapjack.Compiler.Backend.BviInline
open BviSem BvlSem

private theorem nonLabelErrorSwap {C D F : Type} (op : ClosLang.Op) (args : List Value)
    (source : BviState C F) (target : BviState D F)
    (error : SemanticPrimitivesHOL.ErrorResult ExnOrRet)
    (notInstall : op ≠ .install) (notLabel : ∀ n, op ≠ .label n)
    (run : BviSem.doApp op args source = .err error)
    (domain : (∀ key, sptDomain target.code key → sptDomain source.code key) ∨
      error ≠ .abort .typeError) :
    BviSem.doApp op args (runtimeFrame source target) = .err error := by
  have frame := doAppAux_frame op args source target (Or.inr notLabel)
  have fallbackSource : BviSem.doApp op args source = doAppFallback op args source := by
    cases op <;> simp_all [BviSem.doApp]
  have fallbackTarget : BviSem.doApp op args (runtimeFrame source target) =
      doAppFallback op args (runtimeFrame source target) := by
    cases op <;> simp_all [BviSem.doApp]
  rw [fallbackSource] at run
  rw [fallbackTarget]
  unfold doAppFallback at run ⊢
  rw [frame]
  cases aux : doAppAux op args source with
  | none => simp_all
  | some result =>
    cases result with
    | some pair => simp_all
    | none =>
      simp only [aux, Option.map_some, Option.map_none] at run ⊢
      have notGlobal : ∀ operation, op ≠ .globOp operation := by
        intro operation eq
        subst op
        exact doAppAux_delegates_not_global operation args source aux
      rw [toBvl_runtimeFrame]
      cases original : BvlSem.doApp op args (toBvl source) with
      | val pair => simp [original] at run
      | err err =>
        have domain' : (∀ key, sptDomain (toBvl (runtimeFrame source target)).code key →
              sptDomain (toBvl source).code key) ∨ err ≠ .abort .typeError := by
          rcases domain with subset | nonType
          · left
            intro key present
            simpa [toBvl_domain, runtimeFrame] using subset key (by simpa [toBvl_domain, runtimeFrame] using present)
          · right
            intro eq
            subst err
            simp [original] at run
            exact nonType run.symm
        have swapped := BvlProps.doAppFallbackRerrSwap op args (toBvl source) err
          (toBvl (runtimeFrame source target)) notGlobal ⟨original, notInstall, domain'⟩
        rw [swapped]
        cases err <;> simp_all

namespace StateSwapCarrier
/-- The BVI reference carrier has a canonical finite-support roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviSem.BviState C F, BviSem.BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end StateSwapCarrier

/-- A non-install error is preserved by swapping runtime fields when the
original domain or non-type-error condition holds. The dispatcher inherits
the real-model assumption documented in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "do_app_state_swap_Rerr"
  (fmap_as_finite_support := [refs])]
theorem doAppStateSwapRerr {C D F : Type} (op : ClosLang.Op) (args : List Value)
    (source : BviState C F) (target : BviState D F)
    (error : SemanticPrimitivesHOL.ErrorResult ExnOrRet)
    (premises : op ≠ .install ∧ BviSem.doApp op args source = .err error ∧
      ((∀ key, sptDomain target.code key → sptDomain source.code key) ∨
        error ≠ .abort .typeError)) :
    BviSem.doApp op args { target with
      refs := source.refs
      clock := source.clock
      global := source.global
      ffi := source.ffi } = .err error := by
  change BviSem.doApp op args (runtimeFrame source target) = .err error
  obtain ⟨notInstall, run, domain⟩ := premises
  by_cases isLabel : ∃ n, op = .label n
  · obtain ⟨name, rfl⟩ := isLabel
    cases args with
    | cons value rest => simpa [BviSem.doApp, doAppFallback, doAppAux] using run
    | nil =>
      cases sourceLookup : sptLookup name source.code with
      | some entry => simp [BviSem.doApp, doAppFallback, doAppAux, sourceLookup] at run
      | none =>
        simp [BviSem.doApp, doAppFallback, doAppAux, sourceLookup] at run
        subst error
        have subset := domain.resolve_right (by simp)
        cases targetLookup : sptLookup name target.code with
        | none => simp [BviSem.doApp, doAppFallback, doAppAux, runtimeFrame, targetLookup]
        | some entry =>
          have present := subset name (by simp [sptDomain, targetLookup])
          simp [sptDomain, sourceLookup] at present
  · have notLabel : ∀ n, op ≠ .label n := by
      intro n eq
      exact isLabel ⟨n, eq⟩
    exact nonLabelErrorSwap op args source target error notInstall notLabel run domain

end Flapjack.Compiler.Backend.BviInline
