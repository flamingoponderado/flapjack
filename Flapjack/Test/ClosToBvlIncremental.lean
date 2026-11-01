import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Incremental

/-! Concrete checks of the disabled-optimization incremental wrapper. -/
namespace Flapjack.Test.ClosToBvlIncremental
open Flapjack.Compiler.Backend
open ClosToBvl

private def config : Config :=
  { defaultConfig with nextLoc := 10, maxApp := 2, doMti := false, doCall := false, knownConf := none }

/-- Incremental compilation keeps incoming auxiliary code, allocates the
entry label, and advances the numbering state. -/
example : (match compileIncNoOpts? config ([.var .none 0], [(42, 0, .var .none 0)]) with
    | some (out, [(15, 0, .var 0), (47, 0, .var 0)]) => out.nextLoc == 12
    | _ => false) = true := by native_decide

/-- Enabled optimizations are rejected until their incremental passes are
connected to this wrapper. -/
example : compileIncNoOpts? { config with doMti := true } ([], []) = none := by rfl
example : compileIncNoOpts? { config with doCall := true } ([], []) = none := by rfl
example : compileIncNoOpts? { config with knownConf := some (ClosKnown.defaultConfig 2) } ([], []) = none := by rfl

end Flapjack.Test.ClosToBvlIncremental
