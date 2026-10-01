import Flapjack.Compiler.Backend.Parmove.AllDistinct.Pmov

namespace Flapjack.Test.ParmoveAllDistinctPmovParity
open Compiler.Backend.Parmove

/-! Kernel replay of complete existing original parmove_final_probe outputs
terminal/self/chain/cycle/active, with genuine applications of the full
ALL_DISTINCT_pmov captured in parmove_preservation_shape_probe.out.
No fresh original execution is claimed. -/

private def terminalState : State Nat := ([],[],[(some 7,none)])
example : pmov terminalState = ([],[],[(some 7,none)]) ∧
    ((((pmov terminalState).1 ++ (pmov terminalState).2.1 ++ (pmov terminalState).2.2).map Prod.fst).filter Option.isSome).Nodup := by
  have valid : wf terminalState := by simp [terminalState, wf, windmill, path]
  have distinct : (((terminalState.1 ++ terminalState.2.1 ++ terminalState.2.2).map Prod.fst).filter Option.isSome).Nodup := by decide
  exact ⟨by simp [terminalState, pmov.eq_def], allDistinctPmov terminalState ⟨valid, distinct⟩⟩

private def selfState : State Nat := ([(some 1,some 1)],[],[])
example : pmov selfState = ([],[],[]) ∧
    ((((pmov selfState).1 ++ (pmov selfState).2.1 ++ (pmov selfState).2.2).map Prod.fst).filter Option.isSome).Nodup := by
  have valid : wf selfState := by simp [selfState, wf, windmill, path]
  have distinct : (((selfState.1 ++ selfState.2.1 ++ selfState.2.2).map Prod.fst).filter Option.isSome).Nodup := by decide
  exact ⟨by simp [selfState, pmov.eq_def, fstep], allDistinctPmov selfState ⟨valid, distinct⟩⟩

private def chainState : State Nat := ([(some 1,some 2),(some 2,some 3)],[],[])
example : pmov chainState = ([],[],[(some 2,some 3),(some 1,some 2)]) ∧
    ((((pmov chainState).1 ++ (pmov chainState).2.1 ++ (pmov chainState).2.2).map Prod.fst).filter Option.isSome).Nodup := by
  have valid : wf chainState := by simp [chainState, wf, windmill, path]
  have distinct : (((chainState.1 ++ chainState.2.1 ++ chainState.2.2).map Prod.fst).filter Option.isSome).Nodup := by decide
  exact ⟨by simp [chainState, pmov.eq_def, fstep, splitSource], allDistinctPmov chainState ⟨valid, distinct⟩⟩

private def cycleState : State Nat := ([(some 1,some 2),(some 2,some 1)],[],[])
example : pmov cycleState = ([],[],[(some 1,none),(some 2,some 1),(none,some 2)]) ∧
    ((((pmov cycleState).1 ++ (pmov cycleState).2.1 ++ (pmov cycleState).2.2).map Prod.fst).filter Option.isSome).Nodup := by
  have valid : wf cycleState := by simp [cycleState, wf, windmill, path]
  have distinct : (((cycleState.1 ++ cycleState.2.1 ++ cycleState.2.2).map Prod.fst).filter Option.isSome).Nodup := by decide
  exact ⟨by simp [cycleState, pmov.eq_def, fstep, splitSource, frontLast], allDistinctPmov cycleState ⟨valid, distinct⟩⟩

private def activeState : State Nat := ([],[(some 1,some 2),(some 2,none)],[(none,some 1)])
example : pmov activeState = ([],[],[(some 2,none),(some 1,some 2),(none,some 1)]) ∧
    ((((pmov activeState).1 ++ (pmov activeState).2.1 ++ (pmov activeState).2.2).map Prod.fst).filter Option.isSome).Nodup := by
  have valid : wf activeState := by simp [activeState, wf, windmill, path]
  have distinct : (((activeState.1 ++ activeState.2.1 ++ activeState.2.2).map Prod.fst).filter Option.isSome).Nodup := by decide
  exact ⟨by simp [activeState, pmov.eq_def, fstep, splitSource, frontLast], allDistinctPmov activeState ⟨valid, distinct⟩⟩

private def emptyState : State Nat := ([],[],[])
example : ((((pmov emptyState).1 ++ (pmov emptyState).2.1 ++ (pmov emptyState).2.2).map Prod.fst).filter Option.isSome).Nodup := by
  apply allDistinctPmov emptyState
  exact ⟨by simp [emptyState, wf, windmill, path], by decide⟩

private def scratchHistoryState : State Nat := ([],[],[(none,none),(none,some 2)])
example : ((((pmov scratchHistoryState).1 ++ (pmov scratchHistoryState).2.1 ++ (pmov scratchHistoryState).2.2).map Prod.fst).filter Option.isSome).Nodup := by
  apply allDistinctPmov scratchHistoryState
  exact ⟨by simp [scratchHistoryState, wf, windmill, path], by decide⟩

private def boolState : State Bool := ([(some true,some false)],[],[])
example : ((((pmov boolState).1 ++ (pmov boolState).2.1 ++ (pmov boolState).2.2).map Prod.fst).filter Option.isSome).Nodup := by
  apply allDistinctPmov boolState
  exact ⟨by simp [boolState, wf, windmill, path], by decide⟩

-- wf ignores emitted history, but the theorem must still require its real
-- destinations to be distinct: a duplicate history is not a valid premise.
example : wf (([],[],[(some 1,none),(some 1,some 2)]) : State Nat) := by
  simp [wf, windmill, path]
example : ¬ ((([(some 1,none),(some 1,some 2)] : List (Move Nat)).map Prod.fst).filter Option.isSome).Nodup := by decide

end Flapjack.Test.ParmoveAllDistinctPmovParity
