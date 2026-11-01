import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Incremental

/-! Concrete checks of the disabled-optimization incremental wrapper. -/
namespace Flapjack.Test.ClosToBvlIncremental
open Flapjack.Compiler.Backend
open ClosToBvl
open Flapjack.Basis.Pure.MlString

private def config : Config :=
  { defaultConfig with nextLoc := 10, maxApp := 2, doMti := false, doCall := false, knownConf := none }

private def configWithCalls : Config :=
  { config with callState := (sptInsert 9 () .ln, [(3, 0, .var .none 0)]) }

/-- Incremental compilation keeps incoming auxiliary code, allocates the
entry label, and advances the numbering state. -/
example : (match compileIncNoOpts? config ([.var .none 0], [(42, 0, .var .none 0)]) with
    | some (out, [(15, 0, .var 0), (47, 0, .var 0)]) => out.nextLoc == 12
    | _ => false) = true := by native_decide

/-- Replays `incremental_aux` from the pinned HOL probe, including the
retained call set and discarded old call-state auxiliary list. -/
example : (match compileIncNoOpts? configWithCalls ([.var .none 0], [(42, 0, .var .none 0)]) with
    | some (out, [(15, 0, .var 0), (47, 0, .var 0)]) =>
        out.nextLoc == 12 && decide (sptToAList out.callState.1 = [(9, ())]) && out.callState.2.isEmpty
    | _ => false) = true := by native_decide

/-- Replays the empty-input and single-closure outputs from the same probe. -/
example : (match compileIncNoOpts? config ([], []) with
    | some (out, [(15, 0, .op (.intOp (.const 10)) [])]) => out.nextLoc == 12
    | _ => false) = true := by native_decide

example : (match compileIncNoOpts? config ([.fn (ofString "f") none none 1 (.var .none 0)], []) with
    | some (out, [(15, 0, .op (.blockOp (.cons 30))
          [.op (.intOp (.const 0)) [], .op (.label 17) []]), (17, 2, .let [.var 0] (.var 0))]) =>
        out.nextLoc == 14
    | _ => false) = true := by native_decide

/-- Replays the source's enabled multi-argument case, including removal of
the incoming auxiliary program. -/
example : (match compileIncMtiFuel? 0 { config with doMti := true, maxApp := 3 }
    ([.fn (ofString "f") none none 1 (.fn (ofString "g") none none 1 (.var .none 0))],
      [(42, 0, .var .none 0)]) with
    | some (out, [(18, 0, .op (.blockOp (.cons 30))
          [.op (.intOp (.const 1)) [], .op (.label 20) []]),
        (20, 3, .let [.var 0, .var 1] (.var 0))]) => out.nextLoc == 14
    | _ => false) = true := by native_decide

example : (match compileIncMtiFuel? 0 { config with doMti := true, maxApp := 3 }
    ([], [(42, 0, .var .none 0)]) with
    | some (out, [(18, 0, .op (.intOp (.const 10)) [])]) => out.nextLoc == 12
    | _ => false) = true := by native_decide

/-- Enabled optimizations are rejected until their incremental passes are
connected to this wrapper. -/
example : compileIncNoOpts? { config with doMti := true } ([], []) = none := by rfl
example : compileIncNoOpts? { config with doCall := true } ([], []) = none := by rfl
example : compileIncNoOpts? { config with knownConf := some (ClosKnown.defaultConfig 2) } ([], []) = none := by rfl

private def downstream : BvlSem.Compiler Nat := fun state entries =>
  if entries.length == 2 then some ([BitVec.ofNat 8 state], [], state + 1) else none

/-- The multi-argument callback passes its transformed output downstream. -/
example : (match compileIncMtiFuelCallback 0 downstream ({ config with doMti := true, maxApp := 3 }, 7)
    ([.fn (ofString "f") none none 1 (.fn (ofString "g") none none 1 (.var .none 0))],
      [(42, 0, .var .none 0)]) with
    | some ([byte], [], (next, 8)) => byte == BitVec.ofNat 8 7 && next.nextLoc == 14 && next.doMti
    | _ => false) = true := by native_decide

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
