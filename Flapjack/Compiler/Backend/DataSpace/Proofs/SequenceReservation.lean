import Flapjack.Compiler.Backend.DataSpace.Proofs.Sequence

/-! Composition when adjacent space reservations are combined. -/
namespace Flapjack.Compiler.Backend.DataSpace
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- A leading reservation composes with a second component whose compiled
form begins with a deferred reservation. This is auxiliary infrastructure. -/
theorem simulationFor_seq_makeSpace_deferred {C F : Type} (firstAmount : Nat) (firstNames : NumSet)
    (second : DataLang.Prog) (amount : Nat) (names : NumSet) (body : DataLang.Prog)
    (found : space second = .inr (amount, names, body))
    (secondIH : simulationFor (C := C) (F := F) second) :
    simulationFor (C := C) (F := F) (.seq (.makeSpace firstAmount firstNames) second) := by
  intro source sourceNext result locals notType run included
  cases firstCut : cutEnv firstNames source.locals with
  | none =>
    simp [DataSem.evaluate, firstCut, fixClock] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)
  | some middle =>
    let middleState := addSpace { source with locals := middle } firstAmount
    have firstRun : DataSem.evaluate (.makeSpace firstAmount firstNames) source = (none, middleState) := by
      simp [DataSem.evaluate, firstCut, middleState]
    rw [DataSem.evaluate, fixClock_evaluate, firstRun] at run
    have reflexive : sptSubspt middleState.locals middleState.locals := by
      intro key member
      exact ⟨member, rfl⟩
    obtain ⟨out, safe, peak, stackMax, secondRun, finalIncluded⟩ :=
      secondIH middleState sourceNext result middleState.locals notType run reflexive
    have secondRun' : DataSem.evaluate (.seq (.makeSpace amount names) body) middleState =
        (result, if result = none then { sourceNext with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
          else { sourceNext with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }) := by
      simpa [compile, found, pMakeSpace] using secondRun
    cases secondCut : cutEnv names middle with
    | none =>
      simp [DataSem.evaluate, middleState, addSpace, secondCut, fixClock] at secondRun'
      obtain ⟨rfl, _⟩ := secondRun'
      exact False.elim (notType rfl)
    | some finalEnv =>
      have combined := cutEnv_twice firstNames names source.locals middle finalEnv firstCut secondCut
      have targetCut := cutEnv_of_subspt (sptInter firstNames names) source.locals locals finalEnv included combined
      let bodyStart := addSpace { middleState with locals := finalEnv } amount
      have middleLocals : middleState.locals = middle := rfl
      have secondReserve : DataSem.evaluate (.makeSpace amount names) middleState = (none, bodyStart) := by
        simp [DataSem.evaluate, middleLocals, secondCut, bodyStart]
      rw [DataSem.evaluate, fixClock_evaluate, secondReserve] at secondRun'
      let targetStart := addSpace { source with locals := finalEnv } amount
      have targetShape : targetStart = { bodyStart with safeForSpace := targetStart.safeForSpace, peakHeapLength := targetStart.peakHeapLength, stackMax := targetStart.stackMax } := by
        rfl
      obtain ⟨safe', peak', max', targetBody⟩ := evaluate_resource_variation_exact body bodyStart _ result
        targetStart.safeForSpace targetStart.peakHeapLength targetStart.stackMax notType secondRun'
      rw [← targetShape] at targetBody
      refine ⟨out, safe', peak', max', ?_, finalIncluded⟩
      simp only [compile, space, found, pMakeSpace]
      have targetReserve : DataSem.evaluate (.makeSpace amount (sptInter firstNames names)) { source with locals := locals } = (none, targetStart) := by
        simp [DataSem.evaluate, targetCut, targetStart]
      rw [DataSem.evaluate, fixClock_evaluate, targetReserve]
      cases result <;> simpa using targetBody

/-- Sequencing after a reservation preserves the simulation, whether the
second component has a deferred reservation or not. -/
theorem simulationFor_seq_makeSpace_left {C F : Type} (amount : Nat) (names : NumSet)
    (second : DataLang.Prog) (secondIH : simulationFor (C := C) (F := F) second) :
    simulationFor (C := C) (F := F) (.seq (.makeSpace amount names) second) := by
  cases found : space second with
  | inl body =>
    apply simulationFor_seq_of_evaluate_shape (.makeSpace amount names) second (simulationFor_makeSpace amount names) secondIH
    intro state
    simp only [compile, space, found, pMakeSpace]
    conv_rhs => rw [DataSem.evaluate, fixClock_evaluate, DataSem.evaluate_seq_skip]
    conv_lhs => rw [DataSem.evaluate, fixClock_evaluate]
  | inr payload =>
    obtain ⟨nextAmount, nextNames, body⟩ := payload
    exact simulationFor_seq_makeSpace_deferred amount names second nextAmount nextNames body found secondIH

end Flapjack.Compiler.Backend.DataSpace
