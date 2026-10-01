import Flapjack.Compiler.Backend.Parmove.DestinationMembership
namespace Flapjack.Test.ParmoveDestinationParity
open Flapjack.Compiler.Backend.Parmove
-- pv_destination_terminal
example : (pmov (([],[],[(some 7,none)]) : State Nat)).2.2.map Prod.fst = [some 7] := by
  simp [pmov.eq_def]
example (x : Nat) : some x ∈ (pmov (([],[],[(some 7,none)]) : State Nat)).2.2.map Prod.fst →
    some x ∈ ((([],[],[(some 7,none)]) : State Nat)).1.map Prod.fst ++ ((([],[],[(some 7,none)]) : State Nat)).2.1.map Prod.fst ++ ((([],[],[(some 7,none)]) : State Nat)).2.2.map Prod.fst := by
  simpa only [List.map_append] using memMapFstSndSndPmov (([],[],[(some 7,none)]) : State Nat) x
-- pv_destination_self
example : (pmov (([(some 1,some 1)],[],[]) : State Nat)).2.2.map Prod.fst = [] := by
  simp [pmov.eq_def, fstep]
example (x : Nat) : some x ∈ (pmov (([(some 1,some 1)],[],[]) : State Nat)).2.2.map Prod.fst →
    some x ∈ ((([(some 1,some 1)],[],[]) : State Nat)).1.map Prod.fst ++ ((([(some 1,some 1)],[],[]) : State Nat)).2.1.map Prod.fst ++ ((([(some 1,some 1)],[],[]) : State Nat)).2.2.map Prod.fst := by
  simpa only [List.map_append] using memMapFstSndSndPmov (([(some 1,some 1)],[],[]) : State Nat) x
-- pv_destination_chain
example : (pmov (([(some 1,some 2),(some 2,some 3)],[],[]) : State Nat)).2.2.map Prod.fst = [some 2,some 1] := by
  simp [pmov.eq_def, fstep, splitSource]
example (x : Nat) : some x ∈ (pmov (([(some 1,some 2),(some 2,some 3)],[],[]) : State Nat)).2.2.map Prod.fst →
    some x ∈ ((([(some 1,some 2),(some 2,some 3)],[],[]) : State Nat)).1.map Prod.fst ++ ((([(some 1,some 2),(some 2,some 3)],[],[]) : State Nat)).2.1.map Prod.fst ++ ((([(some 1,some 2),(some 2,some 3)],[],[]) : State Nat)).2.2.map Prod.fst := by
  simpa only [List.map_append] using memMapFstSndSndPmov (([(some 1,some 2),(some 2,some 3)],[],[]) : State Nat) x
-- pv_destination_cycle
example : (pmov (([(some 1,some 2),(some 2,some 1)],[],[]) : State Nat)).2.2.map Prod.fst = [some 1,some 2,none] := by
  simp [pmov.eq_def, fstep, splitSource, frontLast]
example (x : Nat) : some x ∈ (pmov (([(some 1,some 2),(some 2,some 1)],[],[]) : State Nat)).2.2.map Prod.fst →
    some x ∈ ((([(some 1,some 2),(some 2,some 1)],[],[]) : State Nat)).1.map Prod.fst ++ ((([(some 1,some 2),(some 2,some 1)],[],[]) : State Nat)).2.1.map Prod.fst ++ ((([(some 1,some 2),(some 2,some 1)],[],[]) : State Nat)).2.2.map Prod.fst := by
  simpa only [List.map_append] using memMapFstSndSndPmov (([(some 1,some 2),(some 2,some 1)],[],[]) : State Nat) x
-- pv_destination_scratch
example : (pmov (([(none,some 2),(some 1,none)],[],[]) : State Nat)).2.2.map Prod.fst = [none,some 1] := by
  simp [pmov.eq_def, fstep, splitSource, frontLast]
example (x : Nat) : some x ∈ (pmov (([(none,some 2),(some 1,none)],[],[]) : State Nat)).2.2.map Prod.fst →
    some x ∈ ((([(none,some 2),(some 1,none)],[],[]) : State Nat)).1.map Prod.fst ++ ((([(none,some 2),(some 1,none)],[],[]) : State Nat)).2.1.map Prod.fst ++ ((([(none,some 2),(some 1,none)],[],[]) : State Nat)).2.2.map Prod.fst := by
  simpa only [List.map_append] using memMapFstSndSndPmov (([(none,some 2),(some 1,none)],[],[]) : State Nat) x
-- pv_destination_duplicate
example : (pmov (([(some 1,some 2),(some 1,some 3)],[],[]) : State Nat)).2.2.map Prod.fst = [some 1,some 1] := by
  simp [pmov.eq_def, fstep, splitSource]
example (x : Nat) : some x ∈ (pmov (([(some 1,some 2),(some 1,some 3)],[],[]) : State Nat)).2.2.map Prod.fst →
    some x ∈ ((([(some 1,some 2),(some 1,some 3)],[],[]) : State Nat)).1.map Prod.fst ++ ((([(some 1,some 2),(some 1,some 3)],[],[]) : State Nat)).2.1.map Prod.fst ++ ((([(some 1,some 2),(some 1,some 3)],[],[]) : State Nat)).2.2.map Prod.fst := by
  simpa only [List.map_append] using memMapFstSndSndPmov (([(some 1,some 2),(some 1,some 3)],[],[]) : State Nat) x
-- pv_destination_active
example : (pmov (([],[(some 1,some 2),(some 2,none)],[(none,some 1)]) : State Nat)).2.2.map Prod.fst = [some 2,some 1,none] := by
  simp [pmov.eq_def, fstep, splitSource, frontLast]
example (x : Nat) : some x ∈ (pmov (([],[(some 1,some 2),(some 2,none)],[(none,some 1)]) : State Nat)).2.2.map Prod.fst →
    some x ∈ ((([],[(some 1,some 2),(some 2,none)],[(none,some 1)]) : State Nat)).1.map Prod.fst ++ ((([],[(some 1,some 2),(some 2,none)],[(none,some 1)]) : State Nat)).2.1.map Prod.fst ++ ((([],[(some 1,some 2),(some 2,none)],[(none,some 1)]) : State Nat)).2.2.map Prod.fst := by
  simpa only [List.map_append] using memMapFstSndSndPmov (([],[(some 1,some 2),(some 2,none)],[(none,some 1)]) : State Nat) x
end Flapjack.Test.ParmoveDestinationParity
