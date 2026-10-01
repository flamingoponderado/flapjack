import Flapjack.Compiler.Backend.Parmove.SourceMembership
namespace Flapjack.Test.ParmoveSourceParity
open Flapjack.Compiler.Backend.Parmove
-- pv_source_terminal
example : (pmov (([],[],[(some 7,none)]) : State Nat)).2.2.map Prod.snd = [none] := by
  simp [pmov.eq_def]
example (x : Nat) : some x ∈ (pmov (([],[],[(some 7,none)]) : State Nat)).2.2.map Prod.snd →
    some x ∈ ((([],[],[(some 7,none)]) : State Nat)).1.map Prod.snd ++ ((([],[],[(some 7,none)]) : State Nat)).2.1.map Prod.snd ++ ((([],[],[(some 7,none)]) : State Nat)).2.2.map Prod.snd := by
  simpa only [List.map_append] using memMapSndSndSndPmov (([],[],[(some 7,none)]) : State Nat) x
-- pv_source_self
example : (pmov (([(some 1,some 1)],[],[]) : State Nat)).2.2.map Prod.snd = [] := by
  simp [pmov.eq_def, fstep]
example (x : Nat) : some x ∈ (pmov (([(some 1,some 1)],[],[]) : State Nat)).2.2.map Prod.snd →
    some x ∈ ((([(some 1,some 1)],[],[]) : State Nat)).1.map Prod.snd ++ ((([(some 1,some 1)],[],[]) : State Nat)).2.1.map Prod.snd ++ ((([(some 1,some 1)],[],[]) : State Nat)).2.2.map Prod.snd := by
  simpa only [List.map_append] using memMapSndSndSndPmov (([(some 1,some 1)],[],[]) : State Nat) x
-- pv_source_chain
example : (pmov (([(some 1,some 2),(some 2,some 3)],[],[]) : State Nat)).2.2.map Prod.snd = [some 3,some 2] := by
  simp [pmov.eq_def, fstep, splitSource]
example (x : Nat) : some x ∈ (pmov (([(some 1,some 2),(some 2,some 3)],[],[]) : State Nat)).2.2.map Prod.snd →
    some x ∈ ((([(some 1,some 2),(some 2,some 3)],[],[]) : State Nat)).1.map Prod.snd ++ ((([(some 1,some 2),(some 2,some 3)],[],[]) : State Nat)).2.1.map Prod.snd ++ ((([(some 1,some 2),(some 2,some 3)],[],[]) : State Nat)).2.2.map Prod.snd := by
  simpa only [List.map_append] using memMapSndSndSndPmov (([(some 1,some 2),(some 2,some 3)],[],[]) : State Nat) x
-- pv_source_cycle
example : (pmov (([(some 1,some 2),(some 2,some 1)],[],[]) : State Nat)).2.2.map Prod.snd = [none,some 1,some 2] := by
  simp [pmov.eq_def, fstep, splitSource, frontLast]
example (x : Nat) : some x ∈ (pmov (([(some 1,some 2),(some 2,some 1)],[],[]) : State Nat)).2.2.map Prod.snd →
    some x ∈ ((([(some 1,some 2),(some 2,some 1)],[],[]) : State Nat)).1.map Prod.snd ++ ((([(some 1,some 2),(some 2,some 1)],[],[]) : State Nat)).2.1.map Prod.snd ++ ((([(some 1,some 2),(some 2,some 1)],[],[]) : State Nat)).2.2.map Prod.snd := by
  simpa only [List.map_append] using memMapSndSndSndPmov (([(some 1,some 2),(some 2,some 1)],[],[]) : State Nat) x
-- pv_source_scratch
example : (pmov (([(none,some 2),(some 1,none)],[],[]) : State Nat)).2.2.map Prod.snd = [some 2,none] := by
  simp [pmov.eq_def, fstep, splitSource, frontLast]
example (x : Nat) : some x ∈ (pmov (([(none,some 2),(some 1,none)],[],[]) : State Nat)).2.2.map Prod.snd →
    some x ∈ ((([(none,some 2),(some 1,none)],[],[]) : State Nat)).1.map Prod.snd ++ ((([(none,some 2),(some 1,none)],[],[]) : State Nat)).2.1.map Prod.snd ++ ((([(none,some 2),(some 1,none)],[],[]) : State Nat)).2.2.map Prod.snd := by
  simpa only [List.map_append] using memMapSndSndSndPmov (([(none,some 2),(some 1,none)],[],[]) : State Nat) x
-- pv_source_duplicate
example : (pmov (([(some 1,some 2),(some 1,some 3)],[],[]) : State Nat)).2.2.map Prod.snd = [some 3,some 2] := by
  simp [pmov.eq_def, fstep, splitSource]
example (x : Nat) : some x ∈ (pmov (([(some 1,some 2),(some 1,some 3)],[],[]) : State Nat)).2.2.map Prod.snd →
    some x ∈ ((([(some 1,some 2),(some 1,some 3)],[],[]) : State Nat)).1.map Prod.snd ++ ((([(some 1,some 2),(some 1,some 3)],[],[]) : State Nat)).2.1.map Prod.snd ++ ((([(some 1,some 2),(some 1,some 3)],[],[]) : State Nat)).2.2.map Prod.snd := by
  simpa only [List.map_append] using memMapSndSndSndPmov (([(some 1,some 2),(some 1,some 3)],[],[]) : State Nat) x
-- pv_source_active
example : (pmov (([],[(some 1,some 2),(some 2,none)],[(none,some 1)]) : State Nat)).2.2.map Prod.snd = [none,some 2,some 1] := by
  simp [pmov.eq_def, fstep, splitSource, frontLast]
example (x : Nat) : some x ∈ (pmov (([],[(some 1,some 2),(some 2,none)],[(none,some 1)]) : State Nat)).2.2.map Prod.snd →
    some x ∈ ((([],[(some 1,some 2),(some 2,none)],[(none,some 1)]) : State Nat)).1.map Prod.snd ++ ((([],[(some 1,some 2),(some 2,none)],[(none,some 1)]) : State Nat)).2.1.map Prod.snd ++ ((([],[(some 1,some 2),(some 2,none)],[(none,some 1)]) : State Nat)).2.2.map Prod.snd := by
  simpa only [List.map_append] using memMapSndSndSndPmov (([],[(some 1,some 2),(some 2,none)],[(none,some 1)]) : State Nat) x
-- pv_source_history
example : (pmov (([],[],[(none,some 9)]) : State Nat)).2.2.map Prod.snd = [some 9] := by
  simp [pmov.eq_def]
example (x : Nat) : some x ∈ (pmov (([],[],[(none,some 9)]) : State Nat)).2.2.map Prod.snd →
    some x ∈ [some 9] := by
  simpa using memMapSndSndSndPmov (([],[],[(none,some 9)]) : State Nat) x
end Flapjack.Test.ParmoveSourceParity
