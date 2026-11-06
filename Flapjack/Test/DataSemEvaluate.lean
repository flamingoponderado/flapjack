import Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate

/-! Control-flow observations for data-language evaluation. -/
namespace Flapjack.Test.DataSemEvaluate
open Flapjack
open Flapjack.Compiler.Backend
open DataSem

example {C F : Type} (s : State C F) : evaluate .skip s = (none, s) := by
  rw [evaluate]

example {C F : Type} (s : State C F) :
    evaluate .tick { s with clock := 0 } =
      (some (.err (.abort .timeoutError)), flushState true { s with clock := 0 }) := by
  simp [evaluate]

example {C F : Type} (s : State C F) :
    evaluate (.move 3 2) { s with locals := .ln } =
      (some (.err (.abort .typeError)), { s with locals := .ln }) := by
  simp [evaluate, getVar, sptLookup]

example {C F : Type} (s : State C F) :
    evaluate (.return []) s = (some (.val []), flushState false s) := by
  simp [evaluate, getVars]

example {C F : Type} (s : State C F) :
    evaluate (.seq .skip .tick) { s with clock := 0 } =
      (some (.err (.abort .timeoutError)), flushState true { s with clock := 0 }) := by
  simp [evaluate, fixClock]

example {C F : Type} (s : State C F) :
    evaluate (.call none (some 4) [] none) { s with code := .ln } =
      (some (.err (.abort .typeError)), { s with code := .ln }) := by
  simp [evaluate, getVars, findCode, sptLookup]

example {C F : Type} (s : State C F) :
    evaluate (.force none 5 0)
      { s with locals := .ls (.refPtr false 0), refs := .ls (.thunk .evaluated (.number 7)) } =
      (some (.val [.number 7]),
        flushState false { s with locals := .ls (.refPtr false 0), refs := .ls (.thunk .evaluated (.number 7)) }) := by
  simp [evaluate, getVar, sptLookup, destThunk]

/-- A direct tail call executes its callee after consuming a clock tick. -/
example {C F : Type} (s : State C F) :
    (evaluate (.call none (some 0) [] none)
      { s with code := .ls (0, .return []), clock := 1 }).1 = some (.val []) := by
  simp [evaluate, getVars, findCode, sptLookup, callEnv, decClock]

/-- A returning call transfers a raised value to its handler. -/
example {C F : Type} (s : State C F) :
    (evaluate (.call (some ([1], .ln)) (some 0) [0] (some (2, .return [2])))
      { s with locals := .ls (.number 7), code := .ls (1, .raise 0), clock := 1, stack := [] }).1 =
        some (.val [.number 7]) := by
  simp [evaluate, getVars, getVar, findCode, sptLookup, cutEnv, sptMem, sptDomain, sptInter, sptMkWf,
    callEnv, pushEnv, decClock, jumpExc, fixClock, setVar, sptFromList, sptInsert]

end Flapjack.Test.DataSemEvaluate
