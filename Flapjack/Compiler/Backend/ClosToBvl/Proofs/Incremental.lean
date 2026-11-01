import Flapjack.Compiler.Backend.ClosToBvl.Incremental
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Oracle

/-! Correctness infrastructure for the checked incremental wrapper. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- With optional closure optimizations disabled, the checked wrapper
returns the numbered and annotated source-shaped incremental result and the
updated numbering state. This relates Lean implementations; full HOL
correspondence and the unrestricted incremental compiler remain open. -/
theorem compileIncNoOpts_checked (config : Config) (program : ClosSem.Program)
    (noMti : config.doMti = false) (noCall : config.doCall = false)
    (noKnown : config.knownConf = none) :
    compileIncNoOpts? config program =
      some ({ config with nextLoc := (ClosNumber.compileInc config.nextLoc program.1).1, callState := (config.callState.1, []) },
        compileInc config.maxApp
          (ClosAnnotate.compileInc ((ClosNumber.compileInc config.nextLoc program.1).2, program.2))) := by
  let annotated := ClosAnnotate.compileInc ((ClosNumber.compileInc config.nextLoc program.1).2, program.2)
  have checked : compileProg? config.maxApp
      (chainExps (extractName annotated.1).1 (extractName annotated.1).2 ++ annotated.2) =
        some (compileInc config.maxApp annotated) := by
    simpa using compileInc_checked_eq config.maxApp annotated
  dsimp only [annotated] at checked
  simp [compileIncNoOpts?, noMti, noCall, noKnown, ClosNumber.ignoreTable, checked]

end Flapjack.Compiler.Backend.ClosToBvl
