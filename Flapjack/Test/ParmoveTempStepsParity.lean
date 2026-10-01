import Flapjack.Compiler.Backend.Parmove.TempBeforeAssign.Steps
namespace Flapjack.Test.ParmoveTempStepsParity
open Flapjack.Compiler.Backend.Parmove
private def removeSource : State Nat := ([(some 1,some 1)],[],[])
private def removeTarget : State Nat := ([],[],[])
example : Steps removeSource removeTarget ∧ wf removeSource ∧ notUseTempBeforeAssign (removeSource.2.1 ++ removeSource.2.2).reverse = true ∧ wf removeTarget ∧ notUseTempBeforeAssign (removeTarget.2.1 ++ removeTarget.2.2).reverse = true := by
  have transitions : Steps removeSource removeTarget := Relation.ReflTransGen.single (Step.removeSelf (some 1) [] [] [] [])
  have valid : wf removeSource := by simp [removeSource, wf, windmill, path]
  have safe : notUseTempBeforeAssign (removeSource.2.1 ++ removeSource.2.2).reverse = true := by decide
  exact ⟨transitions, valid, safe, stepsNotUseTempBeforeAssign removeSource removeTarget ⟨⟨valid, safe⟩, transitions⟩⟩
private def startSource : State Nat := ([(some 1,some 2)],[],[])
private def startTarget : State Nat := ([],[(some 1,some 2)],[])
example : Steps startSource startTarget ∧ wf startSource ∧ notUseTempBeforeAssign (startSource.2.1 ++ startSource.2.2).reverse = true ∧ wf startTarget ∧ notUseTempBeforeAssign (startTarget.2.1 ++ startTarget.2.2).reverse = true := by
  have transitions : Steps startSource startTarget := Relation.ReflTransGen.single (Step.start (some 1) (some 2) [] [] [])
  have valid : wf startSource := by simp [startSource, wf, windmill, path]
  have safe : notUseTempBeforeAssign (startSource.2.1 ++ startSource.2.2).reverse = true := by decide
  exact ⟨transitions, valid, safe, stepsNotUseTempBeforeAssign startSource startTarget ⟨⟨valid, safe⟩, transitions⟩⟩
private def extendSource : State Nat := ([(some 3,some 1)],[(some 1,some 2)],[])
private def extendTarget : State Nat := ([],[(some 3,some 1),(some 1,some 2)],[])
example : Steps extendSource extendTarget ∧ wf extendSource ∧ notUseTempBeforeAssign (extendSource.2.1 ++ extendSource.2.2).reverse = true ∧ wf extendTarget ∧ notUseTempBeforeAssign (extendTarget.2.1 ++ extendTarget.2.2).reverse = true := by
  have transitions : Steps extendSource extendTarget := Relation.ReflTransGen.single (Step.extend (some 1) (some 3) (some 2) [] [] [] [])
  have valid : wf extendSource := by simp [extendSource, wf, windmill, path]
  have safe : notUseTempBeforeAssign (extendSource.2.1 ++ extendSource.2.2).reverse = true := by decide
  exact ⟨transitions, valid, safe, stepsNotUseTempBeforeAssign extendSource extendTarget ⟨⟨valid, safe⟩, transitions⟩⟩
private def save_cycleSource : State Nat := ([],[(some 1,some 2),(some 2,some 1)],[])
private def save_cycleTarget : State Nat := ([],[(some 1,some 2),(some 2,none)],[(none,some 1)])
example : Steps save_cycleSource save_cycleTarget ∧ wf save_cycleSource ∧ notUseTempBeforeAssign (save_cycleSource.2.1 ++ save_cycleSource.2.2).reverse = true ∧ wf save_cycleTarget ∧ notUseTempBeforeAssign (save_cycleTarget.2.1 ++ save_cycleTarget.2.2).reverse = true := by
  have transitions : Steps save_cycleSource save_cycleTarget := Relation.ReflTransGen.single (Step.save (some 2) (some 1) [] [(some 1,some 2)] [])
  have valid : wf save_cycleSource := by simp [save_cycleSource, wf, windmill, path]
  have safe : notUseTempBeforeAssign (save_cycleSource.2.1 ++ save_cycleSource.2.2).reverse = true := by decide
  exact ⟨transitions, valid, safe, stepsNotUseTempBeforeAssign save_cycleSource save_cycleTarget ⟨⟨valid, safe⟩, transitions⟩⟩
private def emit_headSource : State Nat := ([],[(some 3,some 1),(some 1,some 2)],[])
private def emit_headTarget : State Nat := ([],[(some 1,some 2)],[(some 3,some 1)])
example : Steps emit_headSource emit_headTarget ∧ wf emit_headSource ∧ notUseTempBeforeAssign (emit_headSource.2.1 ++ emit_headSource.2.2).reverse = true ∧ wf emit_headTarget ∧ notUseTempBeforeAssign (emit_headTarget.2.1 ++ emit_headTarget.2.2).reverse = true := by
  have transitions : Steps emit_headSource emit_headTarget := Relation.ReflTransGen.single (Step.emitHead (some 1) (some 3) (some 2) (some 1) [] [] [] (by simp) (by decide))
  have valid : wf emit_headSource := by simp [emit_headSource, wf, windmill, path]
  have safe : notUseTempBeforeAssign (emit_headSource.2.1 ++ emit_headSource.2.2).reverse = true := by decide
  exact ⟨transitions, valid, safe, stepsNotUseTempBeforeAssign emit_headSource emit_headTarget ⟨⟨valid, safe⟩, transitions⟩⟩
private def emit_lastSource : State Nat := ([],[(some 1,some 2)],[])
private def emit_lastTarget : State Nat := ([],[],[(some 1,some 2)])
example : Steps emit_lastSource emit_lastTarget ∧ wf emit_lastSource ∧ notUseTempBeforeAssign (emit_lastSource.2.1 ++ emit_lastSource.2.2).reverse = true ∧ wf emit_lastTarget ∧ notUseTempBeforeAssign (emit_lastTarget.2.1 ++ emit_lastTarget.2.2).reverse = true := by
  have transitions : Steps emit_lastSource emit_lastTarget := Relation.ReflTransGen.single (Step.emitLast (some 1) (some 2) [] [] (by simp))
  have valid : wf emit_lastSource := by simp [emit_lastSource, wf, windmill, path]
  have safe : notUseTempBeforeAssign (emit_lastSource.2.1 ++ emit_lastSource.2.2).reverse = true := by decide
  exact ⟨transitions, valid, safe, stepsNotUseTempBeforeAssign emit_lastSource emit_lastTarget ⟨⟨valid, safe⟩, transitions⟩⟩
private def save_noneSource : State Nat := ([],[(some 1,none)],[(none,some 2)])
private def save_noneTarget : State Nat := ([],[(some 1,none)],[(none,none),(none,some 2)])
example : Steps save_noneSource save_noneTarget ∧ wf save_noneSource ∧ notUseTempBeforeAssign (save_noneSource.2.1 ++ save_noneSource.2.2).reverse = true ∧ wf save_noneTarget ∧ notUseTempBeforeAssign (save_noneTarget.2.1 ++ save_noneTarget.2.2).reverse = true := by
  have transitions : Steps save_noneSource save_noneTarget := Relation.ReflTransGen.single (Step.save (some 1) none [] [] [(none,some 2)])
  have valid : wf save_noneSource := by simp [save_noneSource, wf, windmill, path]
  have safe : notUseTempBeforeAssign (save_noneSource.2.1 ++ save_noneSource.2.2).reverse = true := by decide
  exact ⟨transitions, valid, safe, stepsNotUseTempBeforeAssign save_noneSource save_noneTarget ⟨⟨valid, safe⟩, transitions⟩⟩
private def emit_scratchSource : State Nat := ([],[(some 1,some 2),(some 2,none)],[(none,some 1)])
private def emit_scratchTarget : State Nat := ([],[(some 2,none)],[(some 1,some 2),(none,some 1)])
example : Steps emit_scratchSource emit_scratchTarget ∧ wf emit_scratchSource ∧ notUseTempBeforeAssign (emit_scratchSource.2.1 ++ emit_scratchSource.2.2).reverse = true ∧ wf emit_scratchTarget ∧ notUseTempBeforeAssign (emit_scratchTarget.2.1 ++ emit_scratchTarget.2.2).reverse = true := by
  have transitions : Steps emit_scratchSource emit_scratchTarget := Relation.ReflTransGen.single (Step.emitHead (some 2) (some 1) none (some 2) [] [] [(none,some 1)] (by simp) (by decide))
  have valid : wf emit_scratchSource := by simp [emit_scratchSource, wf, windmill, path]
  have safe : notUseTempBeforeAssign (emit_scratchSource.2.1 ++ emit_scratchSource.2.2).reverse = true := by decide
  exact ⟨transitions, valid, safe, stepsNotUseTempBeforeAssign emit_scratchSource emit_scratchTarget ⟨⟨valid, safe⟩, transitions⟩⟩
private def boolSource : State Bool := ([(some true,some true)],[],[])
private def boolTarget : State Bool := ([],[],[])
example : Steps boolSource boolTarget ∧ wf boolSource ∧ notUseTempBeforeAssign (boolSource.2.1 ++ boolSource.2.2).reverse = true ∧ wf boolTarget ∧ notUseTempBeforeAssign (boolTarget.2.1 ++ boolTarget.2.2).reverse = true := by
  have transitions : Steps boolSource boolTarget := Relation.ReflTransGen.single (Step.removeSelf (some true) [] [] [] [])
  have valid : wf boolSource := by simp [boolSource, wf, windmill, path]
  have safe : notUseTempBeforeAssign (boolSource.2.1 ++ boolSource.2.2).reverse = true := by decide
  exact ⟨transitions, valid, safe, stepsNotUseTempBeforeAssign boolSource boolTarget ⟨⟨valid, safe⟩, transitions⟩⟩
private def refl_emptySource : State Nat := ([],[],[])
private def refl_emptyTarget : State Nat := ([],[],[])
example : Steps refl_emptySource refl_emptyTarget ∧ wf refl_emptySource ∧ notUseTempBeforeAssign (refl_emptySource.2.1 ++ refl_emptySource.2.2).reverse = true ∧ wf refl_emptyTarget ∧ notUseTempBeforeAssign (refl_emptyTarget.2.1 ++ refl_emptyTarget.2.2).reverse = true := by
  have transitions : Steps refl_emptySource refl_emptyTarget := Relation.ReflTransGen.refl
  have valid : wf refl_emptySource := by simp [refl_emptySource, wf, windmill, path]
  have safe : notUseTempBeforeAssign (refl_emptySource.2.1 ++ refl_emptySource.2.2).reverse = true := by decide
  exact ⟨transitions, valid, safe, stepsNotUseTempBeforeAssign refl_emptySource refl_emptyTarget ⟨⟨valid, safe⟩, transitions⟩⟩
private def refl_scratchSource : State Nat := ([],[(some 1,none)],[(none,some 2)])
private def refl_scratchTarget : State Nat := ([],[(some 1,none)],[(none,some 2)])
example : Steps refl_scratchSource refl_scratchTarget ∧ wf refl_scratchSource ∧ notUseTempBeforeAssign (refl_scratchSource.2.1 ++ refl_scratchSource.2.2).reverse = true ∧ wf refl_scratchTarget ∧ notUseTempBeforeAssign (refl_scratchTarget.2.1 ++ refl_scratchTarget.2.2).reverse = true := by
  have transitions : Steps refl_scratchSource refl_scratchTarget := Relation.ReflTransGen.refl
  have valid : wf refl_scratchSource := by simp [refl_scratchSource, wf, windmill, path]
  have safe : notUseTempBeforeAssign (refl_scratchSource.2.1 ++ refl_scratchSource.2.2).reverse = true := by decide
  exact ⟨transitions, valid, safe, stepsNotUseTempBeforeAssign refl_scratchSource refl_scratchTarget ⟨⟨valid, safe⟩, transitions⟩⟩
private def cycle_threeSource : State Nat := ([],[(some 1,some 2),(some 2,some 1)],[])
private def cycle_threeTarget : State Nat := ([],[],[(some 2,none),(some 1,some 2),(none,some 1)])
example : Steps cycle_threeSource cycle_threeTarget ∧ wf cycle_threeSource ∧ notUseTempBeforeAssign (cycle_threeSource.2.1 ++ cycle_threeSource.2.2).reverse = true ∧ wf cycle_threeTarget ∧ notUseTempBeforeAssign (cycle_threeTarget.2.1 ++ cycle_threeTarget.2.2).reverse = true := by
  have transitions : Steps cycle_threeSource cycle_threeTarget := ((Relation.ReflTransGen.single (Step.save (some 2) (some 1) [] [(some 1,some 2)] [])).tail (Step.emitHead (some 2) (some 1) none (some 2) [] [] [(none,some 1)] (by simp) (by decide))).tail (Step.emitLast (some 2) none [] [(some 1,some 2),(none,some 1)] (by simp))
  have valid : wf cycle_threeSource := by simp [cycle_threeSource, wf, windmill, path]
  have safe : notUseTempBeforeAssign (cycle_threeSource.2.1 ++ cycle_threeSource.2.2).reverse = true := by decide
  exact ⟨transitions, valid, safe, stepsNotUseTempBeforeAssign cycle_threeSource cycle_threeTarget ⟨⟨valid, safe⟩, transitions⟩⟩
end Flapjack.Test.ParmoveTempStepsParity
