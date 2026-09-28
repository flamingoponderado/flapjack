import Flapjack.Misc.LList

/-!
# HOL `llist` rendering checks

Behavioural checks of `Flapjack/Misc/LList.lean` against the defining HOL
equations of `HOL/src/coalgebras/llistScript.sml` (`LNTH`, `LTAKE`, `LUNFOLD`,
`fromList`, `LPREFIX` on finite lists).  Bead `flapjack-pxn.18.5.6.34.1.1`.
-/

namespace Flapjack.Test.HolLListParity

open Flapjack Flapjack.HolLList

-- LNTH n (fromList l) = oEL n l
#guard lnth 0 (fromList [1, 2, 3]) == some 1
#guard lnth 2 (fromList [1, 2, 3]) == some 3
#guard lnth 3 (fromList [1, 2, 3]) == none
#guard lnth 0 (lnil : HolLList Nat) == none
-- LTAKE
#guard ltake 2 (fromList [1, 2, 3]) == some [1, 2]
#guard ltake 4 (fromList [1, 2, 3]) == none
#guard ltake 0 (lnil : HolLList Nat) == some []
-- LUNFOLD (λn. if n < 3 then SOME (n + 1, n) else NONE) 0 = fromList [0; 1; 2]
private def count3 : HolLList Nat := lunfold (fun n => if n < 3 then some (n + 1, n) else none) 0
#guard (List.range 5).map (fun i => lnth i count3) == [some 0, some 1, some 2, none, none]
#guard ltake 3 count3 == some [0, 1, 2]
-- an infinite LUNFOLD: every position is defined
private def nats : HolLList Nat := lunfold (fun n => some (n + 1, n)) 0
#guard (List.range 6).map (fun i => lnth i nats) == (List.range 6).map some

-- LPREFIX on finite lists is isPREFIX
example : lprefix (fromList [1, 2]) (fromList [1, 2, 3]) :=
  (lprefix_fromList _ _).2 ⟨[3], rfl⟩
example : ¬ lprefix (fromList [2]) (fromList [1, 2, 3]) := by
  rw [lprefix_fromList]; decide
example : toList (fromList [4, 5]) = some [4, 5] := toList_fromList _

def runChecks : IO Bool := do
  IO.println "PASS HOL llist rendering (LNTH/LTAKE/LUNFOLD/fromList/LPREFIX)"
  pure true

end Flapjack.Test.HolLListParity
