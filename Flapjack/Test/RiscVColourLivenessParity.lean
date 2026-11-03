import Flapjack.RiscV.CorrectnessColour

/-! Regression for the live-set assignment case of CakeML's
    `evaluate_apply_colour`: a source and destination may share one colour
    when the source is read before the write and no other live value clashes. -/

namespace Flapjack.Test.RiscVColourLivenessParity

open Flapjack.RiscV

private def aliasColour (name : Nat) : Nat := if name = 0 then 0 else 1

private def liveAliasColour (name : Nat) : Nat :=
  if name = 0 then 0 else if name = 3 then 2 else 1

example :
    liveAliasColour 3 ≠ liveAliasColour 2 := by
  apply wordColouringRespectsClashes_singleWrite_map_noAlias
    2 [3] liveAliasColour [(2, 1), (3, 2)]
  · decide
  · intro name hname
    rcases hname with rfl | hname
    · simp [lookupNatInfo, liveAliasColour]
    · have : name = 3 := by simpa using hname
      subst name
      simp [lookupNatInfo, liveAliasColour]
  · simp
  · simp

example :
    wordApplyColour liveAliasColour
      (.assign 2 (.const (BitVec.ofNat 64 5))) =
      .assign 1 (.const (BitVec.ofNat 64 5)) := by
  simp [wordApplyColour, wordApplyColourExp, liveAliasColour]

end Flapjack.Test.RiscVColourLivenessParity
