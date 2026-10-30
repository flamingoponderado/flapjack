import Flapjack.Compiler.Backend.BvlInline.Proofs.InlineStateRel
import Flapjack.Compiler.Backend.Semantics.BvlProps.ApplyRuntimeFrame

/-! Primitive application under the BVL inlining state relation. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BvlProps
open Flapjack.SemanticPrimitivesHOL

private theorem frameRelated {C F : Type} (limit : Nat)
    (source : State (Spt (Nat × Bvl.Exp) × C) F) (target : State C F)
    (related : inStateRel limit source target) : runtimeFrame source target = target := by
  have fields := inStateRel_fields limit source target related
  cases source
  cases target
  simp_all [runtimeFrame]

private theorem preserveRelated {C F : Type} (limit : Nat)
    (source next : State (Spt (Nat × Bvl.Exp) × C) F) (target : State C F)
    (related : inStateRel limit source target)
    (frame : next.code = source.code ∧ next.compile = source.compile ∧
      next.compileOracle = source.compileOracle) :
    inStateRel limit next (runtimeFrame next target) := by
  rcases frame with ⟨code, compiler, oracle⟩
  simpa [inStateRel, runtimeFrame, code, compiler, oracle] using related.2.2.2.2

/-- Non-install primitives preserve the inlining relation, including errors.
The installation case of the original local theorem remains open; this
restricted helper is Flapjack infrastructure and is not tagged as that theorem. -/
theorem inDoApp_nonInstall {C F : Type} (limit : Nat)
    (source : State (Spt (Nat × Bvl.Exp) × C) F) (target : State C F)
    (related : inStateRel limit source target) (op : ClosLang.Op) (args : List BvlSem.Value)
    (notInstall : op ≠ .install) :
    match doApp op args source with
    | .err error => doApp op args target = .err error
    | .val (value, next) => ∃ targetNext, inStateRel limit next targetNext ∧
        doApp op args target = .val (value, targetNext) := by
  have frame := frameRelated limit source target related
  have domains := related.2.2.2.2.2.2.2.1
  cases run : doApp op args source with
  | err error =>
    have swapped := doAppRerrSwap op args source error target
      ⟨run, notInstall, by intro key present; rwa [domains] at present⟩
    simpa [frame] using swapped
  | val pair =>
    obtain ⟨value, next⟩ := pair
    have code := doApp_code op args source next value notInstall run
    have swapped := doAppRvalSwap op args source next value target
      ⟨run, notInstall, by intro key present; rwa [domains]⟩
    exact ⟨runtimeFrame next target, preserveRelated limit source next target related code,
      by simpa [frame] using swapped⟩

end Flapjack.Compiler.Backend.BvlInline.Proofs
