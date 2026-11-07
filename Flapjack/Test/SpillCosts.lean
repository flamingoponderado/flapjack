import Flapjack.RiscV.SpillCosts

/-! Regression coverage for CakeML spill costs and canonicalized moves. -/

namespace Flapjack

example :
    wordRaChooseSpillNodeByDegree [(3, 2), (5, 5), (7, 4)] 3 [5, 7] = 5 := by
  decide

example :
    wordRaChooseSpillNode [(3, 100), (5, 20), (7, 30)] [(3, 10), (5, 1), (7, 2)] 3 [5, 7] = 3 := by
  decide

end Flapjack
