import Flapjack.Compiler.Backend.Parmove.StepsCorrect
namespace Flapjack.Test.ParmoveStepsCorrectParity
open Flapjack.Compiler.Backend.Parmove
private def cyclePending : List (Move Nat) := [(some 1,some 2),(some 2,some 1)]
private def cycleEmitted : List (Move Nat) := [(some 1,none),(some 2,some 1),(none,some 2)]
private theorem cycleSteps : Steps (cyclePending,[],[]) ([],[],cycleEmitted) := by
  have first : Steps (cyclePending,[],[]) ([(some 2,some 1)],[(some 1,some 2)],[]) :=
    Relation.ReflTransGen.single (Step.start (some 1) (some 2) [] [(some 2,some 1)] [])
  have second := first.tail (Step.extend (some 1) (some 2) (some 2) [] [] [] [])
  have third := second.tail (Step.save (some 1) (some 2) [] [(some 2,some 1)] [])
  have fourth := third.tail (Step.emitHead (some 1) (some 2) none (some 1) [] []
    [(none,some 2)] (by simp) (by decide))
  exact fourth.tail (Step.emitLast (some 1) none [] [(some 2,some 1),(none,some 2)] (by simp))
example (env : Option Nat → Nat) :
    eqenv (parsem cyclePending env) (seqsem cycleEmitted.reverse env) :=
  steps_correct cyclePending cycleEmitted
    ⟨by simp [cyclePending, windmill], by simp [cyclePending], by simp [cyclePending], cycleSteps⟩ env
private def chainPending : List (Move Nat) := [(some 1,some 2),(some 2,some 3)]
private def chainEmitted : List (Move Nat) := [(some 2,some 3),(some 1,some 2)]
private theorem chainSteps : Steps (chainPending,[],[]) ([],[],chainEmitted) := by
  have first : Steps (chainPending,[],[]) ([(some 2,some 3)],[(some 1,some 2)],[]) :=
    Relation.ReflTransGen.single (Step.start (some 1) (some 2) [] [(some 2,some 3)] [])
  have second := first.tail (Step.emitLast (some 1) (some 2) [(some 2,some 3)] [] (by decide))
  have third := second.tail (Step.start (some 2) (some 3) [] [] [(some 1,some 2)])
  exact third.tail (Step.emitLast (some 2) (some 3) [] [(some 1,some 2)] (by simp))
example (env : Option Nat → Nat) :
    eqenv (parsem chainPending env) (seqsem chainEmitted.reverse env) :=
  steps_correct chainPending chainEmitted
    ⟨by simp [chainPending, windmill], by simp [chainPending], by simp [chainPending], chainSteps⟩ env
private def env : Option Nat → Nat := fun x => match x with
 | none => 99
 | some k => 10*k+7
-- pv_correct_cycle_parallel_1=27
example : parsem [(some 1,some 2),(some 2,some 1)] env (some 1) = 27 := by decide
-- pv_correct_cycle_parallel_2=17
example : parsem [(some 1,some 2),(some 2,some 1)] env (some 2) = 17 := by decide
-- pv_correct_cycle_parallel_temp=99
example : parsem [(some 1,some 2),(some 2,some 1)] env (none) = 99 := by decide
-- pv_correct_cycle_sequential_1=27
example : seqsem (List.reverse [(some 1,none),(some 2,some 1),(none,some 2)]) env (some 1) = 27 := by decide
-- pv_correct_cycle_sequential_2=17
example : seqsem (List.reverse [(some 1,none),(some 2,some 1),(none,some 2)]) env (some 2) = 17 := by decide
-- pv_correct_cycle_sequential_temp=27
example : seqsem (List.reverse [(some 1,none),(some 2,some 1),(none,some 2)]) env (none) = 27 := by decide
-- pv_correct_chain_parallel_1=27
example : parsem [(some 1,some 2),(some 2,some 3)] env (some 1) = 27 := by decide
-- pv_correct_chain_parallel_2=37
example : parsem [(some 1,some 2),(some 2,some 3)] env (some 2) = 37 := by decide
-- pv_correct_chain_parallel_temp=99
example : parsem [(some 1,some 2),(some 2,some 3)] env (none) = 99 := by decide
-- pv_correct_chain_sequential_1=27
example : seqsem (List.reverse [(some 2,some 3),(some 1,some 2)]) env (some 1) = 27 := by decide
-- pv_correct_chain_sequential_2=37
example : seqsem (List.reverse [(some 2,some 3),(some 1,some 2)]) env (some 2) = 37 := by decide
-- pv_correct_chain_sequential_temp=99
example : seqsem (List.reverse [(some 2,some 3),(some 1,some 2)]) env (none) = 99 := by decide
end Flapjack.Test.ParmoveStepsCorrectParity
