import Flapjack.Compiler.Backend.Parmove.SplitSource
namespace Flapjack.Test.ParmoveSplitSourceParity
open Flapjack.Compiler.Backend.Parmove
-- pv_split_empty=([],[])
example : splitSource (α := Nat) (some 1) [] = ([],[]) := by decide
-- pv_split_first=([],[(SOME 7,SOME 1); (SOME 8,SOME 1)])
example : splitSource (α := Nat) (some 1) [(some 7,some 1),(some 8,some 1)] = ([],[(some 7,some 1), (some 8,some 1)]) := by decide
-- pv_split_middle=([(SOME 7,SOME 2)],[(SOME 8,SOME 1); (SOME 9,SOME 1)])
example : splitSource (α := Nat) (some 1) [(some 7,some 2),(some 8,some 1),(some 9,some 1)] = ([(some 7,some 2)],[(some 8,some 1), (some 9,some 1)]) := by decide
-- pv_split_absent=([(SOME 7,SOME 2); (SOME 8,SOME 3)],[])
example : splitSource (α := Nat) (some 1) [(some 7,some 2),(some 8,some 3)] = ([(some 7,some 2), (some 8,some 3)],[]) := by decide
-- pv_split_none=([(SOME 7,SOME 2)],[(SOME 8,NONE); (SOME 9,NONE)])
example : splitSource (α := Nat) (none) [(some 7,some 2),(some 8,none),(some 9,none)] = ([(some 7,some 2)],[(some 8,none), (some 9,none)]) := by decide
-- pv_split_duplicate_dest=([(SOME 7,SOME 2)],[(SOME 7,SOME 1); (SOME 7,SOME 3)])
example : splitSource (α := Nat) (some 1) [(some 7,some 2),(some 7,some 1),(some 7,some 3)] = ([(some 7,some 2)],[(some 7,some 1), (some 7,some 3)]) := by decide
-- pv_split_late_zero=([(NONE,SOME 2)],[(SOME 0,SOME 0)])
example : splitSource (α := Nat) (some 0) [(none,some 2),(some 0,some 0)] = ([(none,some 2)],[(some 0,some 0)]) := by decide
example {α : Type} [DecidableEq α] (destination : Option α) (moves : List (Move α)) :
    destination ∉ (splitSource destination moves).1.map Prod.snd :=
  splitSource_prefix_noRead destination moves
example {α : Type} [DecidableEq α] (destination : Option α) (moves : List (Move α))
    (head : Move α) (tail : List (Move α))
    (found : (splitSource destination moves).2 = head :: tail) : head.2 = destination :=
  splitSource_suffix_match destination moves head tail found
example {α : Type} [DecidableEq α] (destination : Option α) (moves : List (Move α)) :
    (splitSource destination moves).2 = [] ↔ destination ∉ moves.map Prod.snd :=
  splitSource_suffix_nil_iff destination moves
end Flapjack.Test.ParmoveSplitSourceParity
