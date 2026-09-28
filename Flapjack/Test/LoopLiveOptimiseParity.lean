import Flapjack.Pancake.LoopLive

namespace Flapjack.Test.LoopLiveOptimiseParity

/-! Direct parity for `loop_live$optimise` (`loop_liveScript.sml:221`), with
the oracle rows in `scripts/hol-probes/loop_live_optimise_probe.out`. -/
def parityGuard : Bool :=
  (match loopLiveOptimise (.skip : LoopProg Nat) with
  | .mark .skip => true
  | _ => false) &&
  (match loopLiveOptimise (.locValue 3 7 : LoopProg Nat) with
  | .mark .skip => true
  | _ => false) &&
  (match loopLiveOptimise (.seq .skip .skip : LoopProg Nat) with
  | .mark (.seq (.mark .skip) (.mark .skip)) => true
  | _ => false) &&
  (match loopLiveOptimise (.ffi "f" 1 2 3 4 [] : LoopProg Nat) with
  | .mark (.ffi "f" 1 2 3 4 []) => true
  | _ => false) &&
  /- A loop fixed point must seed the body with `union live_in live_out`.
     In Cake this keeps the values needed by a break even when the loop's
     outgoing set is empty. -/
  (match loopLiveOptimise
      (.loop [1, 2, 3] (.break 0) [1, 2, 3] : LoopProg Nat) with
  | .loop [1, 2, 3] (.mark (.break 0)) [] => true
  | _ => false) &&
  /- Cake's fixedpoint shrinks the body with the loop's outgoing live set,
     not the union used only for break/continue context. -/
  (match loopLiveOptimise
      (.loop [1] (.assign 1 (.const 7)) [] : LoopProg Nat) with
  | .loop [] (.mark (.assign 1 (.const 7))) [] => true
  | _ => false) &&
  loopListDeleteSorted [7, 8] [1, 2, 3, 4, 5, 6, 7, 8, 7, 8] =
    [1, 2, 3, 4, 5, 6]

#eval parityGuard
#guard parityGuard

/-- HOL `fixedpoint` takes one strict-growth step for the Return body, then
stabilizes at `{1}`. The enclosing Loop shrink observation is the final row of
the same probe. -/
def shrinkLoopFixedpointOracleGuard : Bool :=
  match loopShrink [] (.loop [1] (.return [1]) [] : LoopProg Nat) [] with
  | (.loop [1] (.return [1]) [], [1]) => true
  | _ => false

#guard shrinkLoopFixedpointOracleGuard

/-- HOL's direct `fixedpoint` NONE case is the no-progress branch for a
non-least initial approximation. This replays the matching explicit
`loopShrinkFixed` fallback sentinel; production Loop shrinking starts at the
least set and is checked above against the `shrink` oracle row. -/
def fixedpointNoneFallbackOracleGuard : Bool :=
  match loopShrinkFixed [] [1] (.skip : LoopProg Nat) [] [] 1 [1] with
  | none => true
  | _ => false

#guard fixedpointNoneFallbackOracleGuard

end Flapjack.Test.LoopLiveOptimiseParity
