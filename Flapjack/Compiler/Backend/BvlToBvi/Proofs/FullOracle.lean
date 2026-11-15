module
public import Flapjack.Compiler.Backend.BvlToBvi.SourcePipeline
public import Flapjack.Compiler.Backend.BackendProps.StateCompiler
@[expose] public section

/-! Whole-pass compiler and oracle transformations. -/
open Flapjack Flapjack.Compiler.Backend
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs

/-- Transform every oracle program through the full incremental pass chain. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "full_co_def"]
def fullCo {I C : Type} (c : BvlToBvi.Config)
    (co : I → (Spt (Nat × Bvl.Exp) × Nat × Nat × Nat × Spt (Nat × Bvi.Exp) × C) ×
      List (Nat × Nat × Bvl.Exp)) : I → C × List (Nat × Nat × Bvi.Exp) :=
  BackendProps.stateCo BviInline.compileIncSource
    (BackendProps.stateCo (BviTmc.compileProgSource c.doTmc)
      (BackendProps.stateCo (BviTailrec.compileProgSource c.doTailrec)
        (BackendProps.stateCo BvlToBvi.compileIncSource
          (BackendProps.stateCo (BvlInline.compileInc c.inlineSizeLimit c.splitMainAtSeq c.expCut) co))))

/-- Compose the full pass chain with a downstream compiler callback. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "full_cc_def"]
def fullCc {C Code Data CNext : Type} (c : BvlToBvi.Config)
    (cc : C → List (Nat × Nat × Bvi.Exp) → Option (Code × Data × CNext)) :=
  BackendProps.stateCc (BvlInline.compileInc c.inlineSizeLimit c.splitMainAtSeq c.expCut)
    (BackendProps.stateCc BvlToBvi.compileIncSource
      (BackendProps.stateCc (BviTailrec.compileProgSource c.doTailrec)
        (BackendProps.stateCc (BviTmc.compileProgSource c.doTmc)
          (BackendProps.stateCc BviInline.compileIncSource cc))))
end Flapjack.Compiler.Backend.BvlToBvi.Proofs
