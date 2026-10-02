import Flapjack.Misc.BalancedMap.AlmostBalanceCorrect
namespace Flapjack.Test.BalancedMapAlmostBalanceCorrectParity
open Flapjack.Misc.BalancedMap
example : almostBalancedL 0 0 ∧ almostBalancedL 1 0 ∧ almostBalancedL 0 0 :=
  almostBalancedLThm 0 0 (by unfold balanced delta; decide)
example : almostBalancedR 0 0 ∧ almostBalancedR 0 1 ∧ almostBalancedR 0 0 :=
  almostBalancedRThm 0 0 (by unfold balanced delta; decide)
example : almostBalancedL 0 1 ∧ almostBalancedL 1 1 ∧ almostBalancedL 0 0 :=
  almostBalancedLThm 0 1 (by unfold balanced delta; decide)
example : almostBalancedR 0 1 ∧ almostBalancedR 0 2 ∧ almostBalancedR 0 1 :=
  almostBalancedRThm 0 1 (by unfold balanced delta; decide)
example : almostBalancedL 1 0 ∧ almostBalancedL 2 0 ∧ almostBalancedL 1 0 :=
  almostBalancedLThm 1 0 (by unfold balanced delta; decide)
example : almostBalancedR 1 0 ∧ almostBalancedR 1 1 ∧ almostBalancedR 0 0 :=
  almostBalancedRThm 1 0 (by unfold balanced delta; decide)
example : almostBalancedL 1 1 ∧ almostBalancedL 2 1 ∧ almostBalancedL 1 0 :=
  almostBalancedLThm 1 1 (by unfold balanced delta; decide)
example : almostBalancedR 1 1 ∧ almostBalancedR 1 2 ∧ almostBalancedR 0 1 :=
  almostBalancedRThm 1 1 (by unfold balanced delta; decide)
example : almostBalancedL 1 3 ∧ almostBalancedL 2 3 ∧ almostBalancedL 1 2 :=
  almostBalancedLThm 1 3 (by unfold balanced delta; decide)
example : almostBalancedR 1 3 ∧ almostBalancedR 1 4 ∧ almostBalancedR 0 3 :=
  almostBalancedRThm 1 3 (by unfold balanced delta; decide)
example : almostBalancedL 3 1 ∧ almostBalancedL 4 1 ∧ almostBalancedL 3 0 :=
  almostBalancedLThm 3 1 (by unfold balanced delta; decide)
example : almostBalancedR 3 1 ∧ almostBalancedR 3 2 ∧ almostBalancedR 2 1 :=
  almostBalancedRThm 3 1 (by unfold balanced delta; decide)
example : almostBalancedL 2 6 ∧ almostBalancedL 3 6 ∧ almostBalancedL 2 5 :=
  almostBalancedLThm 2 6 (by unfold balanced delta; decide)
example : almostBalancedR 2 6 ∧ almostBalancedR 2 7 ∧ almostBalancedR 1 6 :=
  almostBalancedRThm 2 6 (by unfold balanced delta; decide)
example : almostBalancedL 6 2 ∧ almostBalancedL 7 2 ∧ almostBalancedL 6 1 :=
  almostBalancedLThm 6 2 (by unfold balanced delta; decide)
example : almostBalancedR 6 2 ∧ almostBalancedR 6 3 ∧ almostBalancedR 5 2 :=
  almostBalancedRThm 6 2 (by unfold balanced delta; decide)
example : almostBalancedL 3 9 ∧ almostBalancedL 4 9 ∧ almostBalancedL 3 8 :=
  almostBalancedLThm 3 9 (by unfold balanced delta; decide)
example : almostBalancedR 3 9 ∧ almostBalancedR 3 10 ∧ almostBalancedR 2 9 :=
  almostBalancedRThm 3 9 (by unfold balanced delta; decide)
example : almostBalancedL 9 3 ∧ almostBalancedL 10 3 ∧ almostBalancedL 9 2 :=
  almostBalancedLThm 9 3 (by unfold balanced delta; decide)
example : almostBalancedR 9 3 ∧ almostBalancedR 9 4 ∧ almostBalancedR 8 3 :=
  almostBalancedRThm 9 3 (by unfold balanced delta; decide)
example : almostBalancedL 10 30 ∧ almostBalancedL 11 30 ∧ almostBalancedL 10 29 :=
  almostBalancedLThm 10 30 (by unfold balanced delta; decide)
example : almostBalancedR 10 30 ∧ almostBalancedR 10 31 ∧ almostBalancedR 9 30 :=
  almostBalancedRThm 10 30 (by unfold balanced delta; decide)
example : almostBalancedL 30 10 ∧ almostBalancedL 31 10 ∧ almostBalancedL 30 9 :=
  almostBalancedLThm 30 10 (by unfold balanced delta; decide)
example : almostBalancedR 30 10 ∧ almostBalancedR 30 11 ∧ almostBalancedR 29 10 :=
  almostBalancedRThm 30 10 (by unfold balanced delta; decide)
end Flapjack.Test.BalancedMapAlmostBalanceCorrectParity
