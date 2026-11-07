import Flapjack.Compiler.Backend.BviInline.Proofs.InstallRelation
import Flapjack.Compiler.Backend.Semantics.BviSem.ApplyRuntimeFrame

/-! Primitive application under the BVI inlining state relation. -/
namespace Flapjack.Compiler.Backend.BviInline
open BviSem BvlSem

private theorem doApp_eq_fallback {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : BviState C F) (notInstall : op ≠ .install) :
    BviSem.doApp op args state = doAppFallback op args state := by
  cases op <;> simp_all [BviSem.doApp]

/-- Flapjack infrastructure: all non-install primitives transfer between
inliner-related states, preserving both successes and errors. -/
theorem doApp_nonInstall_rel {C F : Type} (source : BviState (Spt (Nat × Bvi.Exp) × C) F)
    (target : BviState C F) (related : InStateRel source target)
    (op : ClosLang.Op) (args : List Value) (notInstall : op ≠ .install) :
    match BviSem.doApp op args source with
    | .err error => BviSem.doApp op args target = .err error
    | .val (value, next) => ∃ targetNext, InStateRel next targetNext ∧
        BviSem.doApp op args target = .val (value, targetNext) := by
  have frameEq : runtimeFrame source target = target := by
    rcases related with ⟨refs, clock, global, ffi, _⟩
    cases source
    cases target
    simp_all [runtimeFrame]
  have domains := related.2.2.2.2.2.2.2.1
  have framed := doAppFallback_frame op args source target notInstall domains.symm
  rw [doApp_eq_fallback op args source notInstall]
  rw [doApp_eq_fallback op args target notInstall]
  cases run : doAppFallback op args source with
  | err error => simpa [run, frameEq] using framed
  | val pair =>
    obtain ⟨value, next⟩ := pair
    have fields := doAppFallback_compiler_fields op args source next value run
    obtain ⟨compiler, oracle, code⟩ := fields
    have nextRel : InStateRel next (runtimeFrame next target) := by
      simpa [InStateRel, runtimeFrame, compiler, oracle, code] using related.2.2.2.2
    exact ⟨runtimeFrame next target, nextRel, by simpa [run, frameEq] using framed⟩

/-- Flapjack infrastructure: the complete primitive application simulation,
including dynamic installation and the evaluator's type-error convention. -/
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
  · have simulation := doApp_nonInstall_rel source target related op args install
    cases result : BviSem.doApp op args source with
    | err error => simpa [result] using fun _ => simulation
    | val pair =>
      obtain ⟨value, next⟩ := pair
      simpa [result] using simulation

end Flapjack.Compiler.Backend.BviInline
