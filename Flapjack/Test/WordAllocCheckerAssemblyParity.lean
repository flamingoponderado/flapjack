import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.Assembly

namespace Flapjack.Test.WordAllocCheckerAssemblyParity
open Flapjack Flapjack.WordAlloc Flapjack.RegAlloc

/-! Same-input kernel replay of mixed original HOL checker observations. The
generic application checks that the complete theorem exposes the original
premises for every program and positive word width, without caller-supplied
induction hypotheses. Finite rows do not prove cross-prover equivalence. -/

example {width : Nat} [NeZero width] (p : WordLangProgHOL (BitVec width)) :
    clashTreeGoal p := by
  intro lt f live flive livein flivein h
  exact clashTreeColouringOk p lt f live flive livein flivein h

private def n : NumSet := sptInsert 1 () .ln
private def e : NumSet := sptInsert 2 () .ln
private def control : WordLangProgHOL (BitVec 64) :=
  .seq (.mustTerminate (.loop n (.seq (.continue 0) (.break 0)) e))
    (.ite .equal 3 (.reg 4) .tick .skip)
private def returning : WordLangProgHOL (BitVec 64) :=
  .call (some ([5],(n,e),.mustTerminate (.seq .tick (.loop n (.continue 0) e)),7,8))
    (some 91) [3,4] none
private def handled : WordLangProgHOL (BitVec 64) :=
  .call (some ([5],(n,e),.seq (.assign 6 (.var 7)) .tick,7,8))
    (some 91) [3] (some (5,.loop n (.break 0) e,9,10))
private def tailIgnored : WordLangProgHOL (BitVec 64) :=
  .call none none [3,4] (some (5,.loop (.bn .ln .ln) .tick (.bn .ln .ln),7,8))

-- ca_control=T
example : checkClashTree id (getClashTree control []) .ln .ln =
    some (getLive control .ln [], getLive control .ln []) := by
  simp only [control, getClashTree, checkClashTree]
  decide +kernel
-- ca_return=T
example : checkClashTree id (getClashTree returning []) .ln .ln =
    some (getLive returning .ln [], getLive returning .ln []) := by
  simp only [returning, getClashTree, checkClashTree]
  decide +kernel
-- ca_handler=T
example : checkClashTree id (getClashTree handled []) .ln .ln =
    some (getLive handled .ln [], getLive handled .ln []) := by
  simp only [handled, getClashTree, checkClashTree]
  decide +kernel
-- ca_tail_ignored=T
example : checkClashTree id (getClashTree tailIgnored []) .ln .ln =
    some (getLive tailIgnored .ln [], getLive tailIgnored .ln []) := by
  simp only [tailIgnored, getClashTree, checkClashTree]
  decide +kernel
-- ca_collision=T
example : checkClashTree (fun _ => 0)
    (getClashTree (.seq .tick (.call none none [3,4] none) :
      WordLangProgHOL (BitVec 64)) []) .ln .ln = none := by
  simp only [getClashTree, checkClashTree]
  decide +kernel

end Flapjack.Test.WordAllocCheckerAssemblyParity
