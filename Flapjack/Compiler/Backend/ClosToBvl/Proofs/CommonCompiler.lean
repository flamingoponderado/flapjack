import Flapjack.Compiler.Backend.ClosToBvl.Common
import Flapjack.Compiler.Backend.ClosKnown.Proofs.CompileSemantics
import Flapjack.Compiler.Backend.BackendProps.StateCompiler
import Flapjack.Compiler.Backend.Semantics.ClosSem.State

/-! The source compiler callback threaded through closure preprocessing. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open BackendProps ClosSem

/-- Compose the original incremental closure passes around a downstream
compiler callback. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "compile_common_inc_def"]
noncomputable def compileCommonInc {C : Type} (config : Config) (cc : Compiler C) :
    Compiler (Nat × (Spt ClosKnown.ValApprox × (NumSet × C))) :=
  pureCc (ClosMti.condCompileInc config.doMti config.maxApp)
    (stateCc (ClosNumber.ignoreTable ClosNumber.compileInc)
      (ClosKnown.knownCc config.knownConf
        (stateCc (ClosCall.condCallCompileInc config.doCall)
          (pureCc ClosAnnotate.compileIncSource cc))))

end Flapjack.Compiler.Backend.ClosToBvl
