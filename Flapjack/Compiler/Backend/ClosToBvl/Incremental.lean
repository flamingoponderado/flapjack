import Flapjack.Compiler.Backend.ClosToBvl.Prepared
import Flapjack.Compiler.Backend.ClosToBvl.ExtractName

/-! Checked incremental closure-to-BVL compilation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Incremental closure compilation when multi-argument introduction,
known-function optimization, and direct-call conversion are disabled.
The incoming auxiliary program is retained, as in the source's disabled
passes. Other configurations fail explicitly; the unrestricted source
incremental compiler and its correspondence remain open. -/
def compileIncNoOpts? (config : Config)
    (program : List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)) :
    Option (Config × List (Nat × Nat × Bvl.Exp)) := do
  if config.doMti || config.doCall then none else
  match config.knownConf with
  | some _ => none
  | none =>
      let (next, numbered) := ClosNumber.ignoreTable ClosNumber.compileInc config.nextLoc program
      let annotated := ClosAnnotate.compileInc numbered
      let (start, expressions) := extractName annotated.1
      let compiled ← compileProg? config.maxApp (chainExps start expressions ++ annotated.2)
      pure ({ config with nextLoc := next, callState := (config.callState.1, []) }, compiled)

end Flapjack.Compiler.Backend.ClosToBvl
