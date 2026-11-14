module

public import Flapjack.Compiler.Backend.BviInline.Proofs.InstallRelation
public import Flapjack.Compiler.Backend.Semantics.BviSem.ApplyRuntimeFrame

@[expose] public section

/-! Primitive application under the BVI inlining state relation. -/
namespace Flapjack.Compiler.Backend.BviInline
open BviSem BvlSem

private theorem doApp_eq_fallback {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : BviState C F) (notInstall : op ≠ .install) :
    BviSem.doApp op args state = doAppFallback op args state := by
  cases op <;> simp_all [BviSem.doApp]

namespace PrimitiveRelationCarrier
/-- The canonical BVI reference-map representation has a roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviSem.BviState C F, BviSem.BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end PrimitiveRelationCarrier

/-- Primitive application preserves the inlining state relation, except that
an original type error imposes no condition on the target. Primitive
application inherits the real-model assumption in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "in_do_app_lemma"
  (fmap_as_finite_support := [refs])]
theorem doApp_rel {C F : Type} (source : BviState (Spt (Nat × Bvi.Exp) × C) F)
    (target : BviState C F) (related : InStateRel source target)
    (op : ClosLang.Op) (args : List Value) :
    match BviSem.doApp op args source with
    | .err error => error ≠ .abort .typeError → BviSem.doApp op args target = .err error
    | .val (value, next) => ∃ targetNext, InStateRel next targetNext ∧
        BviSem.doApp op args target = .val (value, targetNext) := by
  by_cases install : op = .install
  · subst op
    exact doApp_install_rel args source target related
  · have frameEq : runtimeFrame source target = target := by
      rcases related with ⟨refs, clock, global, ffi, _⟩
      cases source
      cases target
      simp_all [runtimeFrame]
    have domains := related.2.2.2.2.2.2.2.1
    have framed := doAppFallback_frame op args source target install domains.symm
    rw [doApp_eq_fallback op args source install]
    rw [doApp_eq_fallback op args target install]
    cases run : doAppFallback op args source with
    | err error => intro _; simpa [run, frameEq] using framed
    | val pair =>
      obtain ⟨value, next⟩ := pair
      have fields := doAppFallback_compiler_fields op args source next value run
      obtain ⟨compiler, oracle, code⟩ := fields
      have nextRel : InStateRel next (runtimeFrame next target) := by
        simpa [InStateRel, runtimeFrame, compiler, oracle, code] using related.2.2.2.2
      exact ⟨runtimeFrame next target, nextRel, by simpa [run, frameEq] using framed⟩

end Flapjack.Compiler.Backend.BviInline
