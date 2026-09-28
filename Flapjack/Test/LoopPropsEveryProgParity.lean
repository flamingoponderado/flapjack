import Flapjack.Pancake.Semantics.LoopProps.EveryProg

/-!
Direct Lean replay of the original HOL EVAL cases in
`scripts/hol-probes/loop_props_every_prog_probe.out` for
`loopProps$every_prog_def` (`loopPropsScript.sml:10-24`). The programs use the
exact width-indexed `HolLoopProg 8` carrier and live sets use `NumSet = Spt Unit`.

The probe predicate fails exactly at `Loop` nodes, so every clause's recursion
(including both `Call` handler branches) is observable.

`everyProgHOL` is `Prop`-valued, so the tagged definition is replayed by the
kernel-checked theorems below. `everyProgBool` is a test-local `Bool` rendering
of the same clauses so the rows are also executable for `runChecks`.
-/

namespace Flapjack.Test.LoopPropsEveryProgParity

open Flapjack

private def noloop (program : HolLoopProg 8) : Prop :=
  match program with
  | .loop _ _ _ => False
  | _ => True

private def noloopB (program : HolLoopProg 8) : Bool :=
  match program with
  | .loop _ _ _ => false
  | _ => true

private def everyProgBool (predicate : HolLoopProg 8 → Bool) :
    HolLoopProg 8 → Bool
  | .seq first second =>
      predicate (.seq first second) && everyProgBool predicate first &&
        everyProgBool predicate second
  | .loop liveIn body liveOut =>
      predicate (.loop liveIn body liveOut) && everyProgBool predicate body
  | .ite operator condition right thenBranch elseBranch live =>
      predicate (.ite operator condition right thenBranch elseBranch live) &&
        everyProgBool predicate thenBranch && everyProgBool predicate elseBranch
  | .mark body =>
      predicate (.mark body) && everyProgBool predicate body
  | .call returns target arguments handler =>
      predicate (.call returns target arguments handler) &&
        (match handler with
         | some (_, first, second, _) =>
             everyProgBool predicate first && everyProgBool predicate second
         | none => true)
  | program => predicate program
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

private def loopLn : HolLoopProg 8 := .loop .ln .skip .ln

private def handledCall (first second : HolLoopProg 8) : HolLoopProg 8 :=
  .call none none [] (some (0, first, second, .ln))

#guard everyProgBool noloopB (.skip : HolLoopProg 8) = true
#guard everyProgBool noloopB (.assign 3 (.var 4) : HolLoopProg 8) = true
#guard everyProgBool noloopB (.seq .skip .skip : HolLoopProg 8) = true
#guard everyProgBool noloopB (.seq .skip loopLn : HolLoopProg 8) = false
#guard everyProgBool noloopB loopLn = false
#guard everyProgBool noloopB
    (.ite .equal 1 (.imm 0) .skip .skip .ln : HolLoopProg 8) = true
#guard everyProgBool noloopB
    (.ite .equal 1 (.imm 0) loopLn .skip .ln : HolLoopProg 8) = false
#guard everyProgBool noloopB (.mark .skip : HolLoopProg 8) = true
#guard everyProgBool noloopB (.mark loopLn : HolLoopProg 8) = false
#guard everyProgBool noloopB (.call none none [] none : HolLoopProg 8) = true
#guard everyProgBool noloopB (handledCall .skip .skip) = true
#guard everyProgBool noloopB (handledCall loopLn .skip) = false
#guard everyProgBool noloopB (handledCall .skip loopLn) = false

theorem everyProgHOL_skip : everyProgHOL noloop (.skip : HolLoopProg 8) := by
  simp [everyProgHOL, noloop]

theorem everyProgHOL_assign :
    everyProgHOL noloop (.assign 3 (.var 4) : HolLoopProg 8) := by
  simp [everyProgHOL, noloop]

theorem everyProgHOL_seq :
    everyProgHOL noloop (.seq .skip .skip : HolLoopProg 8) := by
  simp [everyProgHOL, noloop]

theorem everyProgHOL_seq_loop_false :
    ¬ everyProgHOL noloop (.seq .skip loopLn : HolLoopProg 8) := by
  simp [everyProgHOL, noloop, loopLn]

theorem everyProgHOL_loop_false : ¬ everyProgHOL noloop loopLn := by
  simp [everyProgHOL, noloop, loopLn]

theorem everyProgHOL_ite :
    everyProgHOL noloop (.ite .equal 1 (.imm 0) .skip .skip .ln : HolLoopProg 8) := by
  simp [everyProgHOL, noloop]

theorem everyProgHOL_ite_loop_false :
    ¬ everyProgHOL noloop (.ite .equal 1 (.imm 0) loopLn .skip .ln : HolLoopProg 8) := by
  simp [everyProgHOL, noloop, loopLn]

theorem everyProgHOL_mark :
    everyProgHOL noloop (.mark .skip : HolLoopProg 8) := by
  simp [everyProgHOL, noloop]

theorem everyProgHOL_mark_loop_false :
    ¬ everyProgHOL noloop (.mark loopLn : HolLoopProg 8) := by
  simp [everyProgHOL, noloop, loopLn]

theorem everyProgHOL_call_none :
    everyProgHOL noloop (.call none none [] none : HolLoopProg 8) := by
  simp [everyProgHOL, noloop]

theorem everyProgHOL_call_handler :
    everyProgHOL noloop (handledCall .skip .skip) := by
  simp [everyProgHOL, noloop, handledCall]

theorem everyProgHOL_handler_fst_false :
    ¬ everyProgHOL noloop (handledCall loopLn .skip) := by
  simp [everyProgHOL, noloop, handledCall, loopLn]

theorem everyProgHOL_handler_snd_false :
    ¬ everyProgHOL noloop (handledCall .skip loopLn) := by
  simp [everyProgHOL, noloop, handledCall, loopLn]

def runChecks : IO Bool := do
  let ok :=
    everyProgBool noloopB (.skip : HolLoopProg 8) &&
    everyProgBool noloopB (.assign 3 (.var 4) : HolLoopProg 8) &&
    everyProgBool noloopB (.seq .skip .skip : HolLoopProg 8) &&
    !(everyProgBool noloopB (.seq .skip loopLn : HolLoopProg 8)) &&
    !(everyProgBool noloopB loopLn) &&
    everyProgBool noloopB
      (.ite .equal 1 (.imm 0) .skip .skip .ln : HolLoopProg 8) &&
    !(everyProgBool noloopB
      (.ite .equal 1 (.imm 0) loopLn .skip .ln : HolLoopProg 8)) &&
    everyProgBool noloopB (.mark .skip : HolLoopProg 8) &&
    !(everyProgBool noloopB (.mark loopLn : HolLoopProg 8)) &&
    everyProgBool noloopB (.call none none [] none : HolLoopProg 8) &&
    everyProgBool noloopB (handledCall .skip .skip) &&
    !(everyProgBool noloopB (handledCall loopLn .skip)) &&
    !(everyProgBool noloopB (handledCall .skip loopLn))
  if ok then
    IO.println "PASS loopProps every_prog_def exact HOL rows"
  else
    IO.println "FAIL loopProps every_prog_def exact HOL rows"
  pure ok

end Flapjack.Test.LoopPropsEveryProgParity