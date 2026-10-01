import Flapjack.Compiler.Backend.Parmove.AllDistinct.Step
namespace Flapjack.Test.ParmoveAllDistinctStepParity
open Flapjack.Compiler.Backend.Parmove
private def destinations {α : Type} (s : State α) : List (Option α) :=
  ((s.1 ++ s.2.1 ++ s.2.2).map Prod.fst).filter Option.isSome
private def removeSource : State Nat := ([(some 1,some 1)],[],[])
private def removeTarget : State Nat := ([],[],[])
example : Step removeSource removeTarget ∧ (destinations removeSource).Nodup ∧ (destinations removeTarget).Nodup := by
  have transition : Step removeSource removeTarget := Step.removeSelf (some 1) [] [] [] []
  refine ⟨transition, by decide, ?_⟩
  exact allDistinctStep removeSource removeTarget transition (by decide)
private def startSource : State Nat := ([(some 1,some 2)],[],[])
private def startTarget : State Nat := ([],[(some 1,some 2)],[])
example : Step startSource startTarget ∧ (destinations startSource).Nodup ∧ (destinations startTarget).Nodup := by
  have transition : Step startSource startTarget := Step.start (some 1) (some 2) [] [] []
  refine ⟨transition, by decide, ?_⟩
  exact allDistinctStep startSource startTarget transition (by decide)
private def extendSource : State Nat := ([(some 3,some 1)],[(some 1,some 2)],[])
private def extendTarget : State Nat := ([],[(some 3,some 1),(some 1,some 2)],[])
example : Step extendSource extendTarget ∧ (destinations extendSource).Nodup ∧ (destinations extendTarget).Nodup := by
  have transition : Step extendSource extendTarget := Step.extend (some 1) (some 3) (some 2) [] [] [] []
  refine ⟨transition, by decide, ?_⟩
  exact allDistinctStep extendSource extendTarget transition (by decide)
private def save_cycleSource : State Nat := ([],[(some 1,some 2),(some 2,some 1)],[])
private def save_cycleTarget : State Nat := ([],[(some 1,some 2),(some 2,none)],[(none,some 1)])
example : Step save_cycleSource save_cycleTarget ∧ (destinations save_cycleSource).Nodup ∧ (destinations save_cycleTarget).Nodup := by
  have transition : Step save_cycleSource save_cycleTarget := Step.save (some 2) (some 1) [] [(some 1,some 2)] []
  refine ⟨transition, by decide, ?_⟩
  exact allDistinctStep save_cycleSource save_cycleTarget transition (by decide)
private def emit_headSource : State Nat := ([],[(some 3,some 1),(some 1,some 2)],[])
private def emit_headTarget : State Nat := ([],[(some 1,some 2)],[(some 3,some 1)])
example : Step emit_headSource emit_headTarget ∧ (destinations emit_headSource).Nodup ∧ (destinations emit_headTarget).Nodup := by
  have transition : Step emit_headSource emit_headTarget := Step.emitHead (some 1) (some 3) (some 2) (some 1) [] [] [] (by simp) (by decide)
  refine ⟨transition, by decide, ?_⟩
  exact allDistinctStep emit_headSource emit_headTarget transition (by decide)
private def emit_lastSource : State Nat := ([],[(some 1,some 2)],[])
private def emit_lastTarget : State Nat := ([],[],[(some 1,some 2)])
example : Step emit_lastSource emit_lastTarget ∧ (destinations emit_lastSource).Nodup ∧ (destinations emit_lastTarget).Nodup := by
  have transition : Step emit_lastSource emit_lastTarget := Step.emitLast (some 1) (some 2) [] [] (by simp)
  refine ⟨transition, by decide, ?_⟩
  exact allDistinctStep emit_lastSource emit_lastTarget transition (by decide)
private def save_noneSource : State Nat := ([],[(some 1,none)],[(none,some 2)])
private def save_noneTarget : State Nat := ([],[(some 1,none)],[(none,none),(none,some 2)])
example : Step save_noneSource save_noneTarget ∧ (destinations save_noneSource).Nodup ∧ (destinations save_noneTarget).Nodup := by
  have transition : Step save_noneSource save_noneTarget := Step.save (some 1) none [] [] [(none,some 2)]
  refine ⟨transition, by decide, ?_⟩
  exact allDistinctStep save_noneSource save_noneTarget transition (by decide)
private def emit_scratchSource : State Nat := ([],[(some 1,some 2),(some 2,none)],[(none,some 1)])
private def emit_scratchTarget : State Nat := ([],[(some 2,none)],[(some 1,some 2),(none,some 1)])
example : Step emit_scratchSource emit_scratchTarget ∧ (destinations emit_scratchSource).Nodup ∧ (destinations emit_scratchTarget).Nodup := by
  have transition : Step emit_scratchSource emit_scratchTarget := Step.emitHead (some 2) (some 1) none (some 2) [] [] [(none,some 1)] (by simp) (by decide)
  refine ⟨transition, by decide, ?_⟩
  exact allDistinctStep emit_scratchSource emit_scratchTarget transition (by decide)
private def boolSource : State Bool := ([(some true,some true)],[],[])
private def boolTarget : State Bool := ([],[],[])
example : Step boolSource boolTarget ∧ (destinations boolSource).Nodup ∧ (destinations boolTarget).Nodup := by
  have transition : Step boolSource boolTarget := Step.removeSelf (some true) [] [] [] []
  refine ⟨transition, by decide, ?_⟩
  exact allDistinctStep boolSource boolTarget transition (by decide)
private def scratch_startSource : State Nat := ([(none,some 2)],[],[(none,none),(none,some 3)])
private def scratch_startTarget : State Nat := ([],[(none,some 2)],[(none,none),(none,some 3)])
example : Step scratch_startSource scratch_startTarget ∧ (destinations scratch_startSource).Nodup ∧ (destinations scratch_startTarget).Nodup := by
  have transition : Step scratch_startSource scratch_startTarget := Step.start none (some 2) [] [] [(none,none),(none,some 3)]
  refine ⟨transition, by decide, ?_⟩
  exact allDistinctStep scratch_startSource scratch_startTarget transition (by decide)
private def scratch_saveSource : State Nat := ([],[(none,some 2)],[(none,some 3)])
private def scratch_saveTarget : State Nat := ([],[(none,none)],[(none,some 2),(none,some 3)])
example : Step scratch_saveSource scratch_saveTarget ∧ (destinations scratch_saveSource).Nodup ∧ (destinations scratch_saveTarget).Nodup := by
  have transition : Step scratch_saveSource scratch_saveTarget := Step.save none (some 2) [] [] [(none,some 3)]
  refine ⟨transition, by decide, ?_⟩
  exact allDistinctStep scratch_saveSource scratch_saveTarget transition (by decide)
example : ¬ (destinations ([(some 1,some 2)],[],[(some 1,none)])).Nodup := by decide
end Flapjack.Test.ParmoveAllDistinctStepParity
