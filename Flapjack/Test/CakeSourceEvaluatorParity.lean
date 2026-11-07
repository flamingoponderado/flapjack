import Flapjack.EvaluateHOL.Definition

/-! Concrete observations from the pinned CakeML source evaluator. -/
namespace Flapjack.Test.CakeSourceEvaluatorParity
open Flapjack Flapjack.AstHOL Flapjack.EvaluateHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString

private def ffi : HolFfiState Nat := initialHolFfiState (fun _ state _ bytes => .ret state bytes) 0
private def state (clock : Nat) : State Nat :=
  { clock, refs := [], ffi, nextTypeStamp := 0, nextExnStamp := 0, evalState := none }
private def env : SemEnv Value := { v := nsEmpty, c := nsEmpty }
private def call : AstHOL.Exp :=
  .app .opapp [.fn (ofString "x") (.var (.short (ofString "x"))), .lit (.intLit 9)]

example : (evaluate (state 10) env [.lit (.intLit 7)]).2 = .val [.litv (.intLit 7)] := by
  rw [evaluate]
example : (evaluate (state 10) env [.raise (.lit (.intLit 7))]).2 = .err (.raise (.litv (.intLit 7))) := by
  rw [evaluate, evaluate]
  rfl
example : (evaluate (state 10) env [.if_ (.lit (.intLit 1)) (.lit (.intLit 2)) (.lit (.intLit 3))]).2 =
    .err (.abort .typeError) := by
  rw [evaluate, evaluate]
  rfl
example : (evaluate (state 0) env [call]).2 = .err (.abort .timeoutError) := by
  simp [call, evaluate, fixClock, getOpClass, doOpApp, state, env, nsBind, nsEmpty, headValue, holHd, timeoutError]
example : (evaluate (state 1) env [call]).2 = .val [.litv (.intLit 9)] := by
  simp [call, evaluate, fixClock, decClock, getOpClass, doOpApp, state, env, nsBind, nsLookup, nsEmpty, headValue, holHd]

example : (evaluate (state 1) env [call]).1.clock = 0 := by
  simp [call, evaluate, fixClock, decClock, getOpClass, doOpApp, state, env, nsBind, nsLookup, nsEmpty, headValue, holHd]

example : (evaluateMatch (state 4) env (.litv (.intLit 7))
    [(.pvar (ofString "x"), .var (.short (ofString "x")))] bindExnV).2 =
      .val [.litv (.intLit 7)] := by
  simp [evaluateMatch, evaluate, state, env, patBindings, pmatch, nsAppend,
    alistToNs, nsEmpty, nsLookup]

example : (evaluateMatch (state 4) env (.litv (.intLit 7)) [] bindExnV).2 =
    .err (.raise bindExnV) := by rw [evaluateMatch]

example : (match (evaluateDecs (state 4) env
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "x")) (.lit (.intLit 7))]).2 with
    | .val result => nsLookup result.v (.short (ofString "x"))
    | .err _ => none) = some (.litv (.intLit 7)) := by
  simp [evaluateDecs, evaluate, state, env, patBindings, everyExp, oneConCheck,
    pmatch, headValue, holHd, alistToNs, nsEmpty, nsLookup]

end Flapjack.Test.CakeSourceEvaluatorParity
