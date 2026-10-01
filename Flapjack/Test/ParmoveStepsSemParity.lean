import Flapjack.Compiler.Backend.Parmove.StepsSem
namespace Flapjack.Test.ParmoveStepsSemParity
open Flapjack.Compiler.Backend.Parmove
private def initial : State Nat := ([],[(some 1,some 2),(some 2,some 1)],[])
private def saved : State Nat := ([],[(some 1,some 2),(some 2,none)],[(none,some 1)])
private def headEmitted : State Nat := ([],[(some 2,none)],[(some 1,some 2),(none,some 1)])
private def finished : State Nat := ([],[],[(some 2,none),(some 1,some 2),(none,some 1)])
private theorem chain : Steps initial finished := by
  have first : Steps initial saved := Relation.ReflTransGen.single
    (Step.save (some 2) (some 1) [] [(some 1,some 2)] [])
  have second : Steps initial headEmitted := first.tail
    (Step.emitHead (some 2) (some 1) none (some 2) [] [] [(none,some 1)]
      (by simp) (by decide))
  exact second.tail (Step.emitLast (some 2) none [] [(some 1,some 2),(none,some 1)] (by simp))
example (env : Option Nat → Nat) : eqenv (sem initial env) (sem finished env) :=
  steps_sem initial finished ⟨chain, by simp [initial, wf, windmill, path]⟩ env
example (env : Option Nat → Nat) : eqenv (sem initial env) (sem initial env) :=
  steps_sem initial initial ⟨Relation.ReflTransGen.refl, by simp [initial, wf, windmill, path]⟩ env
private def env : Option Nat → Nat := fun x => match x with
 | none => 99
 | some k => 10*k+7
-- pv_rtc_0_1=27
example : sem ([],[(some 1,some 2),(some 2,some 1)],[]) env (some 1) = 27 := by decide
-- pv_rtc_0_2=17
example : sem ([],[(some 1,some 2),(some 2,some 1)],[]) env (some 2) = 17 := by decide
-- pv_rtc_0_temp=99
example : sem ([],[(some 1,some 2),(some 2,some 1)],[]) env (none) = 99 := by decide
-- pv_rtc_1_1=27
example : sem ([],[(some 1,some 2),(some 2,none)],[(none,some 1)]) env (some 1) = 27 := by decide
-- pv_rtc_1_2=17
example : sem ([],[(some 1,some 2),(some 2,none)],[(none,some 1)]) env (some 2) = 17 := by decide
-- pv_rtc_1_temp=17
example : sem ([],[(some 1,some 2),(some 2,none)],[(none,some 1)]) env (none) = 17 := by decide
-- pv_rtc_2_1=27
example : sem ([],[(some 2,none)],[(some 1,some 2),(none,some 1)]) env (some 1) = 27 := by decide
-- pv_rtc_2_2=17
example : sem ([],[(some 2,none)],[(some 1,some 2),(none,some 1)]) env (some 2) = 17 := by decide
-- pv_rtc_2_temp=17
example : sem ([],[(some 2,none)],[(some 1,some 2),(none,some 1)]) env (none) = 17 := by decide
-- pv_rtc_3_1=27
example : sem ([],[],[(some 2,none),(some 1,some 2),(none,some 1)]) env (some 1) = 27 := by decide
-- pv_rtc_3_2=17
example : sem ([],[],[(some 2,none),(some 1,some 2),(none,some 1)]) env (some 2) = 17 := by decide
-- pv_rtc_3_temp=17
example : sem ([],[],[(some 2,none),(some 1,some 2),(none,some 1)]) env (none) = 17 := by decide
end Flapjack.Test.ParmoveStepsSemParity
