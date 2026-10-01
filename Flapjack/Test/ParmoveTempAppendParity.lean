import Flapjack.Compiler.Backend.Parmove.TempBeforeAssign.Append

namespace Flapjack.Test.ParmoveTempAppendParity
open Flapjack.Compiler.Backend.Parmove
private def observation (first second : List (Move Nat)) : Bool × Bool × Bool × Bool :=
  (notUseTempBeforeAssign (first ++ second), notUseTempBeforeAssign first, first.all (fun move => move.1.isSome), notUseTempBeforeAssign second)
-- nta_empty=(T,T,T,T)
example : observation [] [] = (true,true,true,true) := rfl
-- nta_empty_bad=(F,T,T,F)
example : observation [] [(some 1,none)] = (false,true,true,false) := rfl
-- nta_real_bad=(F,T,T,F)
example : observation [(some 1,some 2)] [(some 3,none)] = (false,true,true,false) := rfl
-- nta_write_stops=(T,T,F,F)
example : observation [(none,some 1)] [(some 3,none)] = (true,true,false,false) := rfl
-- nta_read_first=(F,F,T,T)
example : observation [(some 1,none)] [(none,some 2)] = (false,false,true,true) := rfl
-- nta_both_none=(F,F,F,T)
example : observation [(none,none)] [(none,some 2)] = (false,false,false,true) := rfl
-- nta_real_write=(T,T,T,T)
example : observation [(some 1,some 2),(some 3,some 4)] [(none,some 2)] = (true,true,true,true) := rfl
-- nta_late_write=(T,T,F,F)
example : observation [(some 1,some 2),(none,some 3)] [(some 4,none)] = (true,true,false,false) := rfl

example {α : Type} (first second : List (Move α)) := notUseTempBeforeAssignAppend first second

end Flapjack.Test.ParmoveTempAppendParity
