import Flapjack.Pancake.Semantics.LoopProps.CompSyntaxOk

namespace Flapjack

private def compSyntaxLive : NumSet := sptInsert 0 () .ln

/-- Direct Lean replay of the base and Loop clauses. -/
example : compSyntaxOkHOL (width := 8) compSyntaxLive
    (.skip : HolLoopProg 8) = true := by simp [compSyntaxOkHOL]

example : compSyntaxOkHOL compSyntaxLive
    (.loop compSyntaxLive .skip compSyntaxLive : HolLoopProg 8) = true := by
  simp [compSyntaxOkHOL, compSyntaxLive]

example : compSyntaxOkHOL compSyntaxLive
    (.loop .ln .skip compSyntaxLive : HolLoopProg 8) = false := by
  simp [compSyntaxOkHOL, compSyntaxLive]

/-- The Seq clause reuses the first statement's `cut_sets` result for the
    second statement; these rows replay the positive and negative HOL cases. -/
example : compSyntaxOkHOL (width := 8) compSyntaxLive
    (.seq .skip .skip : HolLoopProg 8) = true := by
  simp [compSyntaxOkHOL]

example : compSyntaxOkHOL compSyntaxLive
    (.seq (.loop .ln .skip compSyntaxLive) .skip : HolLoopProg 8) = false := by
  simp [compSyntaxOkHOL, compSyntaxLive]

/-- HOL `EVAL` leaves the `If` witness existential symbolic. These equalities
    replay that residual condition exactly over the faithful Spt carrier. -/
example : compSyntaxOkHOL (width := 8) compSyntaxLive
    (.ite .equal 1 (.reg 2) .skip .skip compSyntaxLive : HolLoopProg 8) =
      holPropBool (∃ names : List Nat,
        compSyntaxLive = sptListInsert names compSyntaxLive) := by
  simp [compSyntaxOkHOL]

example : compSyntaxOkHOL (width := 8) compSyntaxLive
    (.ite .equal 1 (.reg 2) .skip .skip .ln : HolLoopProg 8) =
      holPropBool (∃ names : List Nat,
        (Spt.ln : NumSet) = sptListInsert names compSyntaxLive) := by
  simp [compSyntaxOkHOL]

end Flapjack
