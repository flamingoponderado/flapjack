import Flapjack.Pancake.Semantics.LoopProps.CompSyntax

namespace Flapjack.Test

open Flapjack

private def compSyntaxSeed : NumSet := sptInsert 8 () .ln
private def compSyntaxExtended : NumSet := sptInsert 3 () compSyntaxSeed

-- Direct original HOL EVAL rows are in
-- scripts/hol-probes/loop_props_comp_syntax_ok_probe.out.
example : compSyntaxOkHOLExact (width := 8) compSyntaxSeed
    (.skip : HolLoopProg 8) = true := rfl

example : compSyntaxOkHOLExact (width := 8) compSyntaxSeed
    (.assign 4 (.const 0) : HolLoopProg 8) = true := rfl

example : compSyntaxOkHOLExact (width := 8) compSyntaxSeed
    (.locValue 3 4 : HolLoopProg 8) = true := rfl

example : compSyntaxOkHOLExact (width := 8) compSyntaxSeed
    (.load32 5 6 : HolLoopProg 8) = true := rfl

example : compSyntaxOkHOLExact (width := 8) compSyntaxSeed
    (.loadByte 7 9 : HolLoopProg 8) = true := rfl

example : compSyntaxOkHOLExact (width := 8) compSyntaxSeed
    (.loop compSyntaxSeed .skip compSyntaxSeed : HolLoopProg 8) = true := by
  simp [compSyntaxOkHOLExact]

example : compSyntaxOkHOLExact (width := 8) compSyntaxSeed
    (.loop .ln .skip compSyntaxSeed : HolLoopProg 8) = false := by
  simp [compSyntaxOkHOLExact, compSyntaxSeed, sptInsert]

example : compSyntaxOkHOLExact (width := 8) compSyntaxSeed
    (.seq (.assign 3 (.const 0))
      (.loop compSyntaxExtended .skip compSyntaxExtended) : HolLoopProg 8) = true := by
  simp [compSyntaxOkHOLExact, cutSetsHOL, compSyntaxExtended, compSyntaxSeed]

example : compSyntaxOkHOLExact (width := 8) compSyntaxSeed
    (.seq (.assign 3 (.const 0))
      (.loop compSyntaxSeed .skip compSyntaxSeed) : HolLoopProg 8) = false := by
  simp [compSyntaxOkHOLExact, cutSetsHOL, compSyntaxSeed, sptInsert]

example : compSyntaxOkHOLExact (width := 8) compSyntaxSeed
    (.ite .equal 1 (.reg 2) .skip (.assign 4 (.const 0)) compSyntaxExtended : HolLoopProg 8) = true := by
  classical
  simp only [compSyntaxOkHOLExact, decide_eq_true_eq]
  refine ⟨?_, ?_, ?_⟩
  · trivial
  · trivial
  exact ⟨[3], rfl⟩

example : compSyntaxOkHOLExact (width := 8) compSyntaxSeed
    (.ite .equal 1 (.reg 2) (.loop .ln .skip .ln) .tick compSyntaxSeed : HolLoopProg 8) = false := by
  simp [compSyntaxOkHOLExact, compSyntaxSeed]

example : compSyntaxOkHOLExact (width := 8) compSyntaxSeed
    (.arith (.div 7 8 9) : HolLoopProg 8) = true := rfl

example : compSyntaxOkHOLExact (width := 8) compSyntaxSeed
    (.break 11 : HolLoopProg 8) = true := rfl

example : compSyntaxOkHOLExact (width := 8) compSyntaxSeed
    (.call none none [] none : HolLoopProg 8) = false := rfl

end Flapjack.Test
