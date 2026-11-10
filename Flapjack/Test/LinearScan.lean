module

public import Flapjack.RiscV.LinearScan

@[expose] public section

/-! Regression coverage for the linear-scan live-tree boundary. -/

namespace Flapjack

example :
    wordGetLiveTree
      (.delta [1, 2] [3] : WordClashTree) =
      .seq (.reads [3]) (.writes [1, 2]) := by
  decide +kernel

example :
    wordGetLiveBackward
      (.seq (.writes [1]) (.reads [1, 2])) [] = [2] := by
  decide +kernel

example :
    wordLiveTreeRegisters
      (.branch (.reads [1, 2]) (.writes [2, 3])) = [1, 2, 3] := by
  decide +kernel

example :
    wordIntervalAddIfLt [4] 3 [(4, 5)] =
      [(4, 3)] := by
  decide

example :
    wordIntervalAddIfGt [4] 7 [(4, 5)] =
      [(4, 7)] := by
  decide

example :
    wordGetIntervals
      (.seq (.reads [1]) (.writes [1])) 2 [] [] =
      (0, [(1, 2)], [(1, 2)]) := by
  decide +kernel

example :
    wordIntervalIntersect (2, 5) (4, 8) = true := by
  decide

example :
    wordLinearScanSortRegisters [(1, 2), (5, 0)] [1, 5] = [5, 1] := by
  decide +kernel

example :
    (wordCheckLiveTree id (.seq (.reads [1, 2]) (.writes [1])) [] []).isSome =
      true := by
  decide +kernel

example :
    wordFixLiveTree (.reads [1, 2]) =
      .seq (.writes [1, 2]) (.reads [1, 2]) := by
  decide +kernel

end Flapjack
