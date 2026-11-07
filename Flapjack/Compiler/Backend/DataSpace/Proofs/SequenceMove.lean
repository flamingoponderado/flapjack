import Flapjack.Compiler.Backend.DataSpace.Proofs.SequenceReservation
import Flapjack.Compiler.Backend.Semantics.DataProps.LocalsExtension

/-! Hoisting deferred reservations across moves. -/
namespace Flapjack.Compiler.Backend.DataSpace
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- A move followed by an arbitrary component with a deferred reservation
preserves the data-space simulation. -/
theorem simulationFor_seq_move_deferred {C F : Type} (dest src : Nat) (second : DataLang.Prog)
    (amount : Nat) (names : NumSet) (body : DataLang.Prog)
    (found : space second = .inr (amount, names, body))
    (secondIH : simulationFor (C := C) (F := F) second) :
    simulationFor (C := C) (F := F) (.seq (.move dest src) second) := by
  intro source sourceNext result locals notType run included
  cases read : DataSem.getVar src source.locals with
  | none =>
    simp [DataSem.evaluate, read, fixClock] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)
  | some value =>
    let moved := setVar dest value source
    have moveRun : DataSem.evaluate (.move dest src) source = (none, moved) := by
      simp [DataSem.evaluate, read, moved]
    rw [DataSem.evaluate, fixClock_evaluate, moveRun] at run
    have reflexive : sptSubspt moved.locals moved.locals := by
      intro key member
      exact ⟨member, rfl⟩
    obtain ⟨out, safe, peak, stackMax, secondRun, finalIncluded⟩ :=
      secondIH moved sourceNext result moved.locals notType run reflexive
    have secondRun' : DataSem.evaluate (.seq (.makeSpace amount names) body) moved =
        (result, if result = none then { sourceNext with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
          else { sourceNext with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }) := by
      simpa [compile, found, pMakeSpace] using secondRun
    cases cut : cutEnv names moved.locals with
    | none =>
      simp [DataSem.evaluate, cut, fixClock] at secondRun'
      obtain ⟨rfl, _⟩ := secondRun'
      exact False.elim (notType rfl)
    | some finalEnv =>
      have sourceCut : cutEnv names (sptInsert dest value source.locals) = some finalEnv := by simpa [moved, setVar] using cut
      obtain ⟨before, beforeCut, beforeRead, afterIncluded⟩ :=
        cutEnv_before_move source.locals locals names dest src value finalEnv included read sourceCut
      let bodyStart := addSpace { moved with locals := finalEnv } amount
      have reserveRun : DataSem.evaluate (.makeSpace amount names) moved = (none, bodyStart) := by
        simp [DataSem.evaluate, cut, bodyStart]
      rw [DataSem.evaluate, fixClock_evaluate, reserveRun] at secondRun'
      have bodyIncluded : sptSubspt bodyStart.locals (sptInsert dest value before) := by
        simpa [bodyStart, addSpace] using afterIncluded
      obtain ⟨out', safe', peak', max', extendedRun, finalExtended⟩ :=
        evaluate_locals_extension body bodyStart _ result (sptInsert dest value before) notType secondRun' bodyIncluded
      let targetPre := addSpace { source with locals := before } amount
      let targetStart := setVar dest value targetPre
      let extendedStart := { bodyStart with locals := sptInsert dest value before }
      have targetShape : targetStart = { extendedStart with safeForSpace := targetStart.safeForSpace, peakHeapLength := targetStart.peakHeapLength, stackMax := targetStart.stackMax } := by
        rfl
      obtain ⟨safe'', peak'', max'', varied⟩ := evaluate_resource_variation_exact body extendedStart _ result
        targetStart.safeForSpace targetStart.peakHeapLength targetStart.stackMax notType extendedRun
      rw [← targetShape] at varied
      refine ⟨out', safe'', peak'', max'', ?_, ?_⟩
      · simp only [compile, space, found, pMakeSpace]
        have targetReserve : DataSem.evaluate (.makeSpace amount (sptInsert src () (sptDelete dest names))) { source with locals := locals } = (none, targetPre) := by
          simp [DataSem.evaluate, beforeCut, targetPre]
        have targetMove : DataSem.evaluate (.move dest src) targetPre = (none, targetStart) := by
          simp [DataSem.evaluate, DataSem.getVar, targetPre, addSpace, beforeRead, targetStart, setVar]
        rw [DataSem.evaluate, fixClock_evaluate, targetReserve, DataSem.evaluate, fixClock_evaluate, targetMove]
        cases result <;> simpa using varied
      · cases result with
        | none =>
          exact sptSubsptTrans _ _ _ ⟨finalIncluded, by simpa using finalExtended⟩
        | some stopped =>
          simpa using finalExtended

/-- A move composes with any simulated second component. -/
theorem simulationFor_seq_move_left {C F : Type} (dest src : Nat) (second : DataLang.Prog)
    (secondIH : simulationFor (C := C) (F := F) second) :
    simulationFor (C := C) (F := F) (.seq (.move dest src) second) := by
  cases found : space second with
  | inl body =>
    apply simulationFor_seq_withoutDeferred (.move dest src) second body (simulationFor_move dest src) secondIH found
    · simp
    · intros; simp
  | inr payload =>
    obtain ⟨amount, names, body⟩ := payload
    exact simulationFor_seq_move_deferred dest src second amount names body found secondIH

end Flapjack.Compiler.Backend.DataSpace
