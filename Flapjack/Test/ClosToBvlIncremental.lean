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

private def downstream : BvlSem.Compiler Nat := fun state entries =>
  if entries.length == 2 then some ([BitVec.ofNat 8 state], [], state + 1) else none

/-- The composed callback sends the generated entries to the downstream
compiler and returns both updated configurations. -/
example : (match compileIncNoOptsCallback downstream (config, 7)
    ([.var .none 0], [(42, 0, .var .none 0)]) with
    | some ([byte], [], (next, 8)) => byte == BitVec.ofNat 8 7 && next.nextLoc == 12
    | _ => false) = true := by native_decide

/-- Downstream compilation failure remains a failure. -/
example : (match compileIncNoOptsCallback (C := Nat) (fun _ _ => none) (config, 7)
    ([.var .none 0], [(42, 0, .var .none 0)]) with
    | none => true
    | some _ => false) = true := by native_decide

/-- The oracle adapter retains the downstream configuration and compiled
main and auxiliary entries. -/
example : (match compileIncNoOptsOracle (fun _ => ((config, 7),
    ([.var .none 0], [(42, 0, .var .none 0)]))) 0 with
    | some (7, [(15, 0, .var 0), (47, 0, .var 0)]) => true
    | _ => false) = true := by native_decide

end Flapjack.Test.ClosToBvlIncremental
