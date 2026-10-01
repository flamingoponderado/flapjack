import Flapjack.Compiler.Backend.Parmove.TempBeforeAssign.Pmov

namespace Flapjack.Test.ParmoveTempPmovParity
open Compiler.Backend.Parmove

/-! Non-vacuous theorem applications on the actual scheduler, including four
whole outputs captured in parmove_final_probe.out (pv_final_self/chain/cycle/active).
The original full theorem is captured as pm_audit_pmov_not_use_temp_before_assign
in parmove_preservation_shape_probe.out. No fresh original execution claimed. -/

private def selfState : State Nat := ([(some 1,some 1)],[],[])
example : pmov selfState = ( [], [], [] ) ∧
    notUseTempBeforeAssign ((pmov selfState).2.1 ++ (pmov selfState).2.2).reverse = true := by
  have valid : wf selfState := by simp [selfState, wf, windmill, path]
  have safe : notUseTempBeforeAssign (selfState.2.1 ++ selfState.2.2).reverse = true := by decide
  exact ⟨by simp [selfState, pmov.eq_def, fstep],
    pmovNotUseTempBeforeAssign selfState (fun n : Nat => n + 1) ⟨valid, safe⟩⟩

private def chainState : State Nat := ([(some 1,some 2),(some 2,some 3)],[],[])
example : pmov chainState = ([],[],[(some 2,some 3),(some 1,some 2)]) ∧
    notUseTempBeforeAssign ((pmov chainState).2.1 ++ (pmov chainState).2.2).reverse = true := by
  have valid : wf chainState := by simp [chainState, wf, windmill, path]
  have safe : notUseTempBeforeAssign (chainState.2.1 ++ chainState.2.2).reverse = true := by decide
  exact ⟨by simp [chainState, pmov.eq_def, fstep, splitSource],
    pmovNotUseTempBeforeAssign chainState (fun n : Nat => n + 1) ⟨valid, safe⟩⟩

private def cycleState : State Nat := ([(some 1,some 2),(some 2,some 1)],[],[])
example : pmov cycleState = ([],[],[(some 1,none),(some 2,some 1),(none,some 2)]) ∧
    notUseTempBeforeAssign ((pmov cycleState).2.1 ++ (pmov cycleState).2.2).reverse = true := by
  have valid : wf cycleState := by simp [cycleState, wf, windmill, path]
  have safe : notUseTempBeforeAssign (cycleState.2.1 ++ cycleState.2.2).reverse = true := by decide
  exact ⟨by simp [cycleState, pmov.eq_def, fstep, splitSource, frontLast],
    pmovNotUseTempBeforeAssign cycleState (fun n : Nat => n + 1) ⟨valid, safe⟩⟩

private def activeState : State Nat := ([],[(some 1,some 2),(some 2,none)],[(none,some 1)])
example : pmov activeState = ([],[],[(some 2,none),(some 1,some 2),(none,some 1)]) ∧
    notUseTempBeforeAssign ((pmov activeState).2.1 ++ (pmov activeState).2.2).reverse = true := by
  have valid : wf activeState := by simp [activeState, wf, windmill, path]
  have safe : notUseTempBeforeAssign (activeState.2.1 ++ activeState.2.2).reverse = true := by decide
  exact ⟨by simp [activeState, pmov.eq_def, fstep, splitSource, frontLast],
    pmovNotUseTempBeforeAssign activeState (fun n : Nat => n + 1) ⟨valid, safe⟩⟩

private def emptyState : State Nat := ([],[],[])
example : notUseTempBeforeAssign ((pmov emptyState).2.1 ++ (pmov emptyState).2.2).reverse = true := by
  apply pmovNotUseTempBeforeAssign emptyState ()
  exact ⟨by simp [emptyState, wf, windmill, path], by decide⟩

private def initializedHistoryState : State Nat := ([],[],[(none,some 7)])
example : notUseTempBeforeAssign ((pmov initializedHistoryState).2.1 ++ (pmov initializedHistoryState).2.2).reverse = true := by
  apply pmovNotUseTempBeforeAssign initializedHistoryState ()
  exact ⟨by simp [initializedHistoryState, wf, windmill, path], by decide⟩

private def priorScratchState : State Nat := ([],[(some 1,none)],[(none,some 2)])
example : notUseTempBeforeAssign ((pmov priorScratchState).2.1 ++ (pmov priorScratchState).2.2).reverse = true := by
  apply pmovNotUseTempBeforeAssign priorScratchState ()
  exact ⟨by simp [priorScratchState, wf, windmill, path], by decide⟩

private def boolState : State Bool := ([(some true,some false)],[],[])
example : notUseTempBeforeAssign ((pmov boolState).2.1 ++ (pmov boolState).2.2).reverse = true := by
  apply pmovNotUseTempBeforeAssign boolState ()
  exact ⟨by simp [boolState, wf, windmill, path], by decide⟩

-- The original unsafe terminal row does not satisfy the safety premise.
example : notUseTempBeforeAssign ([(some 7,none)] : List (Move Nat)).reverse = false := by decide

-- Original pending scratch/duplicate rows violate wf; they are not vacuous
-- successful applications of this conditional preservation theorem.
example : ¬ wf (([(none,some 2),(some 1,none)],[],[]) : State Nat) := by
  simp [wf, windmill]
example : ¬ wf (([(some 1,some 2),(some 1,some 3)],[],[]) : State Nat) := by
  simp [wf, windmill]

end Flapjack.Test.ParmoveTempPmovParity
