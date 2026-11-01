import Flapjack.Compiler.Backend.DataLive.Proofs.CallTail

/-! Non-tail call-frame relations for the data liveness proof. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Entering a non-tail call with identical arguments preserves the state
relation and gives equal local environments, regardless of saved locals. -/
theorem stateRel_nonTailEntry {C F : Type} (source target : State C F) (live : NumSet)
    (args : List DataSem.Value) (size : Option Nat) (sourceEnv targetEnv : Spt DataSem.Value) (hasHandler : Bool)
    (related : stateRel source target live) :
    stateRel (DataSem.callEnv args size (pushEnv sourceEnv hasHandler (decClock source)))
      (DataSem.callEnv args size (pushEnv targetEnv hasHandler (decClock target))) .ln ∧
    (DataSem.callEnv args size (pushEnv sourceEnv hasHandler (decClock source))).locals =
      (DataSem.callEnv args size (pushEnv targetEnv hasHandler (decClock target))).locals := by
  rcases related with ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, _⟩
  refine ⟨?_, rfl⟩
  cases hasHandler <;>
    simp [stateRel, DataSem.callEnv, pushEnv, decClock, code, clock, space, ffi, refs, global, handler,
      stack, compiler, oracle, stamps, limits, frames, sptMem, sptDomain, sptLookup]

/-- Restoring corresponding saved control fields preserves the relation at
the saved live set. This generalizes the empty-live auxiliary lemma. -/
theorem stateRel_restoreControl {C F : Type} (source target sourceSaved targetSaved : State C F)
    (live savedLive : NumSet) (related : stateRel source target live)
    (saved : stateRel sourceSaved targetSaved savedLive) :
    stateRel { source with stack := sourceSaved.stack, handler := sourceSaved.handler, locals := sourceSaved.locals, localsSize := sourceSaved.localsSize }
      { target with stack := targetSaved.stack, handler := targetSaved.handler, locals := targetSaved.locals, localsSize := targetSaved.localsSize } savedLive := by
  rcases related with ⟨code, clock, space, ffi, refs, global, _, _, compiler, oracle, stamps, limits, frames, _⟩
  rcases saved with ⟨_, _, _, _, _, _, handler, stack, _, _, _, _, _, locals⟩
  exact ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, locals⟩

/-- A non-tail call without a new handler preserves exception-jump
correspondence through its saved environment frame. -/
theorem exceptionRel_nonTailEntry_noHandler {C F : Type} (source target : State C F) (live : NumSet)
    (args : List DataSem.Value) (size : Option Nat) (sourceEnv targetEnv : Spt DataSem.Value)
    (related : stateRel source target live) (exception : exceptionRel source target) :
    exceptionRel (DataSem.callEnv args size (pushEnv sourceEnv false (decClock source)))
      (DataSem.callEnv args size (pushEnv targetEnv false (decClock target))) := by
  let sourceEntry := DataSem.callEnv args size (pushEnv sourceEnv false (decClock source))
  let targetEntry := DataSem.callEnv args size (pushEnv targetEnv false (decClock target))
  have entryRel := (stateRel_nonTailEntry source target live args size sourceEnv targetEnv false related).1
  intro sourceJump sourceRun
  have mapped : (jumpExc source).map (fun jumped =>
      { sourceEntry with stack := jumped.stack, handler := jumped.handler, locals := jumped.locals, localsSize := jumped.localsSize }) = some sourceJump := by
    rw [← jumpExc_callEnv_push_noHandler source sourceEnv args size]
    exact sourceRun
  cases oldRun : jumpExc source with
  | none => simp [oldRun] at mapped
  | some sourceSaved =>
    simp [oldRun] at mapped
    subst sourceJump
    obtain ⟨targetSaved, targetSavedRun, savedRel, savedHandler, savedStack⟩ := exception sourceSaved oldRun
    let targetJump := { targetEntry with stack := targetSaved.stack, handler := targetSaved.handler, locals := targetSaved.locals, localsSize := targetSaved.localsSize }
    have targetRun : jumpExc targetEntry = some targetJump := by
      rw [jumpExc_callEnv_push_noHandler, targetSavedRun]
      rfl
    refine ⟨targetJump, targetRun, ?_, ?_, ?_⟩
    · exact stateRel_savedControl sourceEntry targetEntry sourceSaved targetSaved .ln entryRel savedRel
    · exact savedHandler
    · exact savedStack

/-- A non-tail call with a fresh handler jumps to its just-saved frame on
both sides, preserving exception correspondence. -/
theorem exceptionRel_nonTailEntry_handler {C F : Type} (source target : State C F) (live : NumSet)
    (args : List DataSem.Value) (size : Option Nat) (sourceEnv targetEnv : Spt DataSem.Value)
    (related : stateRel source target live) :
    exceptionRel (DataSem.callEnv args size (pushEnv sourceEnv true (decClock source)))
      (DataSem.callEnv args size (pushEnv targetEnv true (decClock target))) := by
  let sourceEntry := DataSem.callEnv args size (pushEnv sourceEnv true (decClock source))
  let targetEntry := DataSem.callEnv args size (pushEnv targetEnv true (decClock target))
  intro sourceJump sourceRun
  have sourceExpected := jumpExc_callEnv_push_handler source args size sourceEnv
  have targetExpected := jumpExc_callEnv_push_handler target args size targetEnv
  have sourceEq : sourceJump = { sourceEntry with stack := source.stack, handler := source.handler, locals := sourceEnv, localsSize := source.localsSize } := by
    apply Option.some.inj
    rw [← sourceRun]
    exact sourceExpected
  subst sourceJump
  refine ⟨{ targetEntry with stack := target.stack, handler := target.handler, locals := targetEnv, localsSize := target.localsSize }, targetExpected, ?_, ?_, ?_⟩
  · rcases related with ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, _⟩
    refine ⟨code, ?_, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, ?_⟩
    · simp [sourceEntry, targetEntry, DataSem.callEnv, pushEnv, decClock, clock]
    · intro key member
      simp [sptMem, sptDomain, sptLookup] at member
  · exact related.2.2.2.2.2.2.1.symm
  · exact related.2.2.2.2.2.2.2.1.symm

/-- Returning through corresponding saved frames restores the original
stack and live local relation on both sides. -/
theorem stateRel_popNonTail {C F : Type} (source target sourceLast targetLast : State C F)
    (args : List DataSem.Value) (size : Option Nat) (sourceEnv targetEnv : Spt DataSem.Value)
    (hasHandler : Bool) (live : NumSet)
    (lastRel : stateRel sourceLast targetLast .ln)
    (savedRel : stateRel { source with locals := sourceEnv } { target with locals := targetEnv } live)
    (sourceStack : sourceLast.stack = (DataSem.callEnv args size (pushEnv sourceEnv hasHandler (decClock source))).stack)
    (sourceHandler : sourceLast.handler = (DataSem.callEnv args size (pushEnv sourceEnv hasHandler (decClock source))).handler)
    (targetStack : targetLast.stack = (DataSem.callEnv args size (pushEnv targetEnv hasHandler (decClock target))).stack)
    (targetHandler : targetLast.handler = (DataSem.callEnv args size (pushEnv targetEnv hasHandler (decClock target))).handler) :
    ∃ sourceNext targetNext, popEnv sourceLast = some sourceNext ∧ popEnv targetLast = some targetNext ∧
      stateRel sourceNext targetNext live := by
  let sourceNext := { sourceLast with stack := source.stack, handler := source.handler, locals := sourceEnv, localsSize := source.localsSize }
  let targetNext := { targetLast with stack := target.stack, handler := target.handler, locals := targetEnv, localsSize := target.localsSize }
  have sourcePop : popEnv sourceLast = some sourceNext := by
    cases hasHandler <;> simp [popEnv, sourceStack, sourceHandler, DataSem.callEnv, pushEnv, decClock, sourceNext]
  have targetPop : popEnv targetLast = some targetNext := by
    cases hasHandler <;> simp [popEnv, targetStack, targetHandler, DataSem.callEnv, pushEnv, decClock, targetNext]
  refine ⟨sourceNext, targetNext, sourcePop, targetPop, ?_⟩
  have restored := stateRel_restoreControl sourceLast targetLast
    { source with locals := sourceEnv } { target with locals := targetEnv } .ln live lastRel savedRel
  simpa [sourceNext, targetNext] using restored

end Flapjack.Compiler.Backend.DataLive
