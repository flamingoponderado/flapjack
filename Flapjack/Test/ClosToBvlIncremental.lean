import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Incremental
import Flapjack.Compiler.Backend.ClosToBvl.ToBviIncremental

/-! Concrete checks of the disabled-optimization incremental wrapper. -/
namespace Flapjack.Test.ClosToBvlIncremental
open Flapjack.Compiler.Backend
open ClosToBvl
open Flapjack.Basis.Pure.MlString

private def config : Config :=
  { defaultConfig with nextLoc := 10, maxApp := 2, doMti := false, doCall := false, knownConf := none }

private def configWithCalls : Config :=
  { config with callState := (sptInsert 9 () .ln, [(3, 0, .var .none 0)]) }

private def knownGlobalsConfig : ClosKnown.Config :=
  { ClosKnown.defaultConfig 2 with inlineFactor := 0, valApproxSpt := sptInsert 4 (.int 7) .ln }

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

/-- Replay source direct-call conversion with retained locations and incoming
auxiliary code, which the enabled pass replaces with generated code. -/
example : (match compileIncCallsFuel? 0 { configWithCalls with doCall := true }
    ([.fn (ofString "f") none none 1 (.var .none 0)], [(42, 0, .var .none 0)]) with
    | some (out, [(15, 0, .op (.blockOp (.cons 30))
          [.op (.intOp (.const 0)) [], .op (.label 17) []]),
        (18, 1, .var 0), (17, 2, .let [.var 0] (.call 0 (some 18) [.var 0]))]) =>
        out.nextLoc == 14 && decide (sptToAList out.callState.1 = [(9, ()), (12, ())]) &&
          out.callState.2.isEmpty
    | _ => false) = true := by native_decide

example : (match compileIncCallsFuel? 0 { config with doCall := true, doMti := true, maxApp := 3 }
    ([.fn (ofString "f") none none 1 (.fn (ofString "g") none none 1 (.var .none 0))], []) with
    | some (out, [(18, 0, .op (.blockOp (.cons 30))
          [.op (.intOp (.const 1)) [], .op (.label 20) []]),
        (21, 2, .var 0), (20, 3, .let [.var 0, .var 1] (.call 0 (some 21) [.var 0, .var 1]))]) =>
        out.nextLoc == 14 && decide (sptToAList out.callState.1 = [(12, ())])
    | _ => false) = true := by native_decide

/-- The known pass reads retained global approximations, updates them, resets
the working inline factor, and drops incoming auxiliary code. -/
example : (match compileIncFuel? 100 { config with knownConf := some knownGlobalsConfig }
    ([.op .none (.globOp (.global 4)) [],
      .op .none (.globOp (.setGlobal 5)) [.op .none (.intOp (.const 9)) []]],
      [(42, 0, .var .none 0)]) with
    | some (out, [(15, 0, .let [.op (.intOp (.const 7)) []] (.call 0 (some 16) [])),
        (16, 0, .op (.globOp (.setGlobal 6)) [.op (.intOp (.const 9)) []])]) =>
      out.nextLoc == 12 && match out.knownConf with
        | some known => known.inlineFactor == 0 &&
          match sptLookup 4 known.valApproxSpt, sptLookup 5 known.valApproxSpt with
          | some (.int 7), some (.int 9) => true
          | _, _ => false
        | none => false
    | _ => false) = true := by native_decide

/-- Replay the original default combination of all three optimizations. -/
example : (match compileIncFuel? 100 { defaultConfig with nextLoc := 10, maxApp := 3 }
    ([.fn (ofString "f") none none 1 (.fn (ofString "g") none none 1 (.var .none 0))], []) with
    | some (out, [(18, 0, .op (.blockOp (.cons 30))
          [.op (.intOp (.const 1)) [], .op (.label 20) []]),
        (21, 2, .var 0), (20, 3, .let [.var 0, .var 1] (.call 0 (some 21) [.var 0, .var 1]))]) =>
        out.nextLoc == 14 && decide (sptToAList out.callState.1 = [(12, ())]) &&
          match out.knownConf with
          | some known => (sptToAList known.valApproxSpt).isEmpty
          | none => false
    | _ => false) = true := by native_decide

/-- The composed path carries the closure and BVL configurations into a
subsequent incremental compilation. -/
example : (match compileIncToBviFuel 100 (config, BvlToBvi.defaultConfig)
    ([.var .none 0], []) with
  | some (next, first) =>
    match compileIncToBviFuel 100 next ([.var .none 0], []) with
    | some (last, second) =>
      next.1.nextLoc == 12 && last.1.nextLoc == 14 &&
        !first.isEmpty && !second.isEmpty
    | none => false
  | none => false) = true := by native_decide

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
