import Flapjack.Pancake.Semantics.LoopProps

/-!
Direct Lean replay of the original HOL EVAL cases in
`scripts/hol-probes/loop_props_survives_probe.out` for
`loopProps$survives_def` (`loopPropsScript.sml:25-38`). The programs use the
exact width-indexed `HolLoopProg 8` carrier and live sets use `NumSet = Spt Unit`.
-/

namespace Flapjack.Test.LoopPropsSurvivesParity

open Flapjack
open Flapjack.Basis.Pure.MlString

private def live3 : NumSet := sptInsert 3 () .ln

private def ifProg (live : NumSet) : HolLoopProg 8 :=
  .ite .equal 1 (.imm 0) .skip .skip live

private def loopProg (liveIn liveOut : NumSet) : HolLoopProg 8 :=
  .loop liveIn .skip liveOut

private def callProg (returns : NumSet) : HolLoopProg 8 :=
  .call (some ([], returns)) none [] none

private def handledCallProg (returns post : NumSet) : HolLoopProg 8 :=
  .call (some ([], returns)) none [] (some (0, .skip, .tick, post))

#guard (survivesHOLExact (width := 8) 3 (ifProg live3)) = true
#guard (survivesHOLExact (width := 8) 4 (ifProg live3)) = false
#guard (survivesHOLExact (width := 8) 3 (loopProg live3 live3)) = true
#guard (survivesHOLExact (width := 8) 3 (loopProg live3 .ln)) = false
#guard (survivesHOLExact (width := 8) 3 (callProg live3)) = true
#guard (survivesHOLExact (width := 8) 3 (callProg .ln)) = false
#guard (survivesHOLExact (width := 8) 3 (handledCallProg live3 live3)) = true
#guard (survivesHOLExact (width := 8) 3 (handledCallProg live3 .ln)) = false
#guard (survivesHOLExact (width := 8) 3
    (.ffi (.implode []) 1 2 3 4 live3 : HolLoopProg 8)) = true
#guard (survivesHOLExact (width := 8) 3
    (.ffi (.implode []) 1 2 3 4 .ln : HolLoopProg 8)) = false
#guard (survivesHOLExact (width := 8) 3
    (.mark (.seq .skip .tick) : HolLoopProg 8)) = true
#guard (survivesHOLExact (width := 8) 3
    (.call none none [] none : HolLoopProg 8)) = true
#guard (survivesHOLExact (width := 8) 3
    (.assign 3 (.const (0 : BitVec 8)) : HolLoopProg 8)) = true

def runChecks : IO Bool := do
  let ok :=
    survivesHOLExact (width := 8) 3 (ifProg live3) &&
    !(survivesHOLExact (width := 8) 4 (ifProg live3)) &&
    survivesHOLExact (width := 8) 3 (loopProg live3 live3) &&
    !(survivesHOLExact (width := 8) 3 (loopProg live3 .ln)) &&
    survivesHOLExact (width := 8) 3 (callProg live3) &&
    !(survivesHOLExact (width := 8) 3 (callProg .ln)) &&
    survivesHOLExact (width := 8) 3 (handledCallProg live3 live3) &&
    !(survivesHOLExact (width := 8) 3 (handledCallProg live3 .ln)) &&
    survivesHOLExact (width := 8) 3
      (.ffi (.implode []) 1 2 3 4 live3 : HolLoopProg 8) &&
    !(survivesHOLExact (width := 8) 3
      (.ffi (.implode []) 1 2 3 4 .ln : HolLoopProg 8)) &&
    survivesHOLExact (width := 8) 3
      (.mark (.seq .skip .tick) : HolLoopProg 8) &&
    survivesHOLExact (width := 8) 3
      (.call none none [] none : HolLoopProg 8) &&
    survivesHOLExact (width := 8) 3
      (.assign 3 (.const (0 : BitVec 8)) : HolLoopProg 8)
  if ok then
    IO.println "PASS loopProps survives_def exact HOL cases"
  else
    IO.println "FAIL loopProps survives_def exact HOL cases"
  pure ok

end Flapjack.Test.LoopPropsSurvivesParity
