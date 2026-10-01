import Flapjack.Compiler.Backend.Parmove.TempBeforeAssign.Step
namespace Flapjack.Test.ParmoveTempStepParity
open Flapjack.Compiler.Backend.Parmove
private def removeSource : State Nat := ([(some 1,some 1)],[],[])
private def removeTarget : State Nat := ([],[],[])
-- pts_remove=T: non-vacuous original wf and safety observation.
example : wf removeSource ∧ notUseTempBeforeAssign (removeSource.2.1 ++ removeSource.2.2).reverse = true ∧ notUseTempBeforeAssign (removeTarget.2.1 ++ removeTarget.2.2).reverse = true := by
  refine ⟨?_, ?_, ?_⟩
  · simp [removeSource, wf, windmill, path]
  · decide
  · apply stepNotUseTempBeforeAssign removeSource removeTarget
    · exact Step.removeSelf (some 1) [] [] [] []
    · simp [removeSource, wf, windmill, path]
    · decide
private def startSource : State Nat := ([(some 1,some 2)],[],[])
private def startTarget : State Nat := ([],[(some 1,some 2)],[])
-- pts_start=T: non-vacuous original wf and safety observation.
example : wf startSource ∧ notUseTempBeforeAssign (startSource.2.1 ++ startSource.2.2).reverse = true ∧ notUseTempBeforeAssign (startTarget.2.1 ++ startTarget.2.2).reverse = true := by
  refine ⟨?_, ?_, ?_⟩
  · simp [startSource, wf, windmill, path]
  · decide
  · apply stepNotUseTempBeforeAssign startSource startTarget
    · exact Step.start (some 1) (some 2) [] [] []
    · simp [startSource, wf, windmill, path]
    · decide
private def extendSource : State Nat := ([(some 3,some 1)],[(some 1,some 2)],[])
private def extendTarget : State Nat := ([],[(some 3,some 1),(some 1,some 2)],[])
-- pts_extend=T: non-vacuous original wf and safety observation.
example : wf extendSource ∧ notUseTempBeforeAssign (extendSource.2.1 ++ extendSource.2.2).reverse = true ∧ notUseTempBeforeAssign (extendTarget.2.1 ++ extendTarget.2.2).reverse = true := by
  refine ⟨?_, ?_, ?_⟩
  · simp [extendSource, wf, windmill, path]
  · decide
  · apply stepNotUseTempBeforeAssign extendSource extendTarget
    · exact Step.extend (some 1) (some 3) (some 2) [] [] [] []
    · simp [extendSource, wf, windmill, path]
    · decide
private def save_cycleSource : State Nat := ([],[(some 1,some 2),(some 2,some 1)],[])
private def save_cycleTarget : State Nat := ([],[(some 1,some 2),(some 2,none)],[(none,some 1)])
-- pts_save_cycle=T: non-vacuous original wf and safety observation.
example : wf save_cycleSource ∧ notUseTempBeforeAssign (save_cycleSource.2.1 ++ save_cycleSource.2.2).reverse = true ∧ notUseTempBeforeAssign (save_cycleTarget.2.1 ++ save_cycleTarget.2.2).reverse = true := by
  refine ⟨?_, ?_, ?_⟩
  · simp [save_cycleSource, wf, windmill, path]
  · decide
  · apply stepNotUseTempBeforeAssign save_cycleSource save_cycleTarget
    · exact Step.save (some 2) (some 1) [] [(some 1,some 2)] []
    · simp [save_cycleSource, wf, windmill, path]
    · decide
private def emit_headSource : State Nat := ([],[(some 3,some 1),(some 1,some 2)],[])
private def emit_headTarget : State Nat := ([],[(some 1,some 2)],[(some 3,some 1)])
-- pts_emit_head=T: non-vacuous original wf and safety observation.
example : wf emit_headSource ∧ notUseTempBeforeAssign (emit_headSource.2.1 ++ emit_headSource.2.2).reverse = true ∧ notUseTempBeforeAssign (emit_headTarget.2.1 ++ emit_headTarget.2.2).reverse = true := by
  refine ⟨?_, ?_, ?_⟩
  · simp [emit_headSource, wf, windmill, path]
  · decide
  · apply stepNotUseTempBeforeAssign emit_headSource emit_headTarget
    · exact Step.emitHead (some 1) (some 3) (some 2) (some 1) [] [] [] (by simp) (by decide)
    · simp [emit_headSource, wf, windmill, path]
    · decide
private def emit_lastSource : State Nat := ([],[(some 1,some 2)],[])
private def emit_lastTarget : State Nat := ([],[],[(some 1,some 2)])
-- pts_emit_last=T: non-vacuous original wf and safety observation.
example : wf emit_lastSource ∧ notUseTempBeforeAssign (emit_lastSource.2.1 ++ emit_lastSource.2.2).reverse = true ∧ notUseTempBeforeAssign (emit_lastTarget.2.1 ++ emit_lastTarget.2.2).reverse = true := by
  refine ⟨?_, ?_, ?_⟩
  · simp [emit_lastSource, wf, windmill, path]
  · decide
  · apply stepNotUseTempBeforeAssign emit_lastSource emit_lastTarget
    · exact Step.emitLast (some 1) (some 2) [] [] (by simp)
    · simp [emit_lastSource, wf, windmill, path]
    · decide
private def save_noneSource : State Nat := ([],[(some 1,none)],[(none,some 2)])
private def save_noneTarget : State Nat := ([],[(some 1,none)],[(none,none),(none,some 2)])
-- pts_save_none=T: non-vacuous original wf and safety observation.
example : wf save_noneSource ∧ notUseTempBeforeAssign (save_noneSource.2.1 ++ save_noneSource.2.2).reverse = true ∧ notUseTempBeforeAssign (save_noneTarget.2.1 ++ save_noneTarget.2.2).reverse = true := by
  refine ⟨?_, ?_, ?_⟩
  · simp [save_noneSource, wf, windmill, path]
  · decide
  · apply stepNotUseTempBeforeAssign save_noneSource save_noneTarget
    · exact Step.save (some 1) none [] [] [(none,some 2)]
    · simp [save_noneSource, wf, windmill, path]
    · decide
private def emit_scratchSource : State Nat := ([],[(some 1,some 2),(some 2,none)],[(none,some 1)])
private def emit_scratchTarget : State Nat := ([],[(some 2,none)],[(some 1,some 2),(none,some 1)])
-- pts_emit_scratch=T: non-vacuous original wf and safety observation.
example : wf emit_scratchSource ∧ notUseTempBeforeAssign (emit_scratchSource.2.1 ++ emit_scratchSource.2.2).reverse = true ∧ notUseTempBeforeAssign (emit_scratchTarget.2.1 ++ emit_scratchTarget.2.2).reverse = true := by
  refine ⟨?_, ?_, ?_⟩
  · simp [emit_scratchSource, wf, windmill, path]
  · decide
  · apply stepNotUseTempBeforeAssign emit_scratchSource emit_scratchTarget
    · exact Step.emitHead (some 2) (some 1) none (some 2) [] [] [(none,some 1)] (by simp) (by decide)
    · simp [emit_scratchSource, wf, windmill, path]
    · decide
private def boolSource : State Bool := ([(some true,some true)],[],[])
private def boolTarget : State Bool := ([],[],[])
-- pts_bool=T: non-vacuous original wf and safety observation.
example : wf boolSource ∧ notUseTempBeforeAssign (boolSource.2.1 ++ boolSource.2.2).reverse = true ∧ notUseTempBeforeAssign (boolTarget.2.1 ++ boolTarget.2.2).reverse = true := by
  refine ⟨?_, ?_, ?_⟩
  · simp [boolSource, wf, windmill, path]
  · decide
  · apply stepNotUseTempBeforeAssign boolSource boolTarget
    · exact Step.removeSelf (some true) [] [] [] []
    · simp [boolSource, wf, windmill, path]
    · decide
end Flapjack.Test.ParmoveTempStepParity
