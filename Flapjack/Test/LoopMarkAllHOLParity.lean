import Flapjack.Pancake.LoopLive

/-! Direct parity for the exact `markAllHOL` port of `loop_live$mark_all`
    (`loop_liveScript.sml:189`).  Each row matches a committed original-HOL
    `EVAL` row in `scripts/hol-probes/mark_all_probe.out`, evaluated here over
    the exact `HolLoopProg`/`NumSet` carriers (the production `LoopProg`/`List
    Nat` rendering is covered separately by `LoopMarkAllParity`). -/

namespace Flapjack.Test.LoopMarkAllHOLParity

open Flapjack

private instance : NeZero 8 := ⟨by decide⟩

private abbrev P : Type := HolLoopProg 8

def markAllHOLGuard : Bool :=
  -- seq_mark=(Mark (Seq (Mark Skip) (Mark Skip)),T)
  (match markAllHOL (width := 8) (.seq (.skip : P) (.skip : P)) with
   | (.mark (.seq (.mark .skip) (.mark .skip)), true) => true
   | _ => false) &&
  -- seq_not_mark=(Mark (Seq (Mark Fail) (Mark Skip)),T)
  (match markAllHOL (width := 8) (.seq (.fail : P) (.skip : P)) with
   | (.mark (.seq (.mark .fail) (.mark .skip)), true) => true
   | _ => false) &&
  -- seq_loop_not_mark=(Seq (Loop LN (Mark Skip) LN) (Mark Skip),F)
  (match markAllHOL (width := 8)
      (.seq (.loop (.ln : NumSet) (.skip : P) (.ln : NumSet)) (.skip : P)) with
   | (.seq (.loop .ln (.mark .skip) .ln) (.mark .skip), false) => true
   | _ => false) &&
  -- loop=(Loop LN (Mark Skip) LN,F)
  (match markAllHOL (width := 8) (.loop (.ln : NumSet) (.skip : P) (.ln : NumSet)) with
   | (.loop .ln (.mark .skip) .ln, false) => true
   | _ => false) &&
  -- mark_unwrapped=(Mark Skip,T)
  (match markAllHOL (width := 8) (.mark (.skip : P)) with
   | (.mark .skip, true) => true
   | _ => false) &&
  -- call_no_handler=(Mark (Call NONE NONE [] NONE),T)
  (match markAllHOL (width := 8)
      (.call (none : Option (List Nat × NumSet)) none ([] : List Nat)
        (none : Option (Nat × P × P × NumSet))) with
   | (.mark (.call none none [] none), true) => true
   | _ => false) &&
  -- call_handler=(Mark (Call (SOME ([1],LN)) NONE [2] (SOME (3,Mark Skip,Mark Fail,LN))),T)
  (match markAllHOL (width := 8)
      (.call (some ([1], (.ln : NumSet))) (none : Option Nat) [2]
        (some (3, (.skip : P), (.fail : P), (.ln : NumSet)))) with
   | (.mark (.call (some ([1], .ln)) none [2] (some (3, .mark .skip, .mark .fail, .ln))), true) => true
   | _ => false)

#guard markAllHOLGuard

def runChecks : IO Bool := do
  if markAllHOLGuard then
    IO.println "PASS exact markAllHOL matches all 7 mark_all HOL rows"
  else
    IO.println "FAIL exact markAllHOL matches all 7 mark_all HOL rows"
  pure markAllHOLGuard

end Flapjack.Test.LoopMarkAllHOLParity
