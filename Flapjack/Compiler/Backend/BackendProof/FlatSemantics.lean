module

public import Flapjack.Compiler.Backend.BackendProof.CakeOrac
public import Flapjack.Compiler.Backend.BackendProof.ConfigTuple
public import Flapjack.Compiler.Backend.FlatProps.InstallConfig
public import Flapjack.Compiler.Backend.FlatToClos.Proofs.Semantics
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.NoMat

@[expose] public section

/-! backendProofScript.sml 3401-3417: the flat-to-closure step of the top-level
correctness proof, instantiated at the `cake_orac` flat-program oracle. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.BackendDefs
open Flapjack.Compiler.Backend.BackendProps

/-- Exact HOL `flat_semantics` (`backendProofScript.sml:3401-3417`). HOL's
free `asm_conf`, `c'`, `syn`, `cc`, `ffi`, `ds` and `cconf` are explicit; the
compiler state type of `cc` is the captured
`num # val_approx num_map # num_set # (num # bvl$exp) num_map # num # num #
num # (num # bvi$exp) num_map # num # lab_to_target$config`, the type of
`SND (config_tuple1 c')`. `FEMPTY` is the canonical empty finite map
`HolFiniteMapExact.holEmpty`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "flat_semantics"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem flatSemantics {width : Nat} [NeZero width] {F : Type}
    (asmConf : AsmConfigExact width) (c' : Flapjack.Compiler.Backend.Backend.Config)
    (syn : Nat → (Nat × Nat) × List AstHOL.Dec)
    (cc : ClosSem.Compiler (Nat × Spt ClosKnown.ValApprox × NumSet × Spt (Nat × Bvl.Exp) ×
      Nat × Nat × Nat × Spt (Nat × Bvi.Exp) × Nat × LabToTarget.Config))
    (ffi : HolFfiState F) (ds : List FlatLang.Exp) (cconf : ClosToBvl.Config) :
    let co := cakeOrac asmConf c' syn (Prod.snd ∘ configTuple1) (fun ps => ps.flatProg)
    let fInst := FlatProps.mkFlatInstallConf (pureCc FlatToClos.incCompileDecs cc) co
    FlatSem.semantics fInst ffi ds ≠ .fail ∧ 0 < cconf.maxApp ∧ FlatProps.noMatDecs ds = true →
      ClosSem.semantics ffi cconf.maxApp HolFiniteMapExact.holEmpty
          (pureCo FlatToClos.incCompileDecs ∘ co) cc (FlatToClos.compileProg ds) =
        FlatSem.semantics fInst ffi ds := by
  intro co fInst ⟨hsafe, hpos, hnomat⟩
  refine FlatToClos.compileSemantics_source ffi cconf.maxApp fInst
    (pureCo FlatToClos.incCompileDecs ∘ co) cc ds ⟨hpos, hnomat, ?_, rfl, rfl⟩ hsafe
  intro i
  exact SourceToFlat.noMat_incCompile _ _ _

end Flapjack.Compiler.Backend.BackendProof
