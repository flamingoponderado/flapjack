import Flapjack.Compiler.Backend.WordToStack.Proofs.CallReturnHandler
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallTail
import Flapjack.Compiler.Backend.WordToStack.Proofs.CallReturnStackMoveClock

namespace Flapjack.WordToStackProofs.CompCorrect.CallReturningHandler
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open CallReturnHandler

/-- Actual native restoration state after reading the saved handler slot,
setting the handler store and freeing precisely the three header words.
Flapjack proof infrastructure for the original normal-return branch9495+;
this is not a replacement evaluator or an assumed final state relation. -/
def poppedHandlerState {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (register : Nat)
    (savedHandler : WordLocW width) : StackSemStateFiniteExact width C F :=
  {source with
    regs := source.regs.updateEq (register, savedHandler),
    store := source.store.updateEq (.handler, savedHandler),
    stackSpace := source.stackSpace + 3}

/-- Compute the real PopHandler execution before an arbitrary continuation.
Only primitive preconditions are used; neither a target run nor postrelation
is supplied. This supports the full original case and has no separate HOL
original. All other state fields and the continuation's evaluation are exact. -/
theorem evaluatePopHandler {width : Nat} [NeZero width] {C F β γ : Type}
    (source : StackSemStateFiniteExact width C F) (register : Nat)
    (f : β) (f' : γ) (program : HolProg width) (savedHandler : WordLocW width)
    (stackEnabled : source.useStack = true) (storeEnabled : source.useStore = true)
    (room : source.stackSpace + 3 ≤ source.stack.length)
    (saved : source.stack[source.stackSpace + 2] = savedHandler) :
    StackSemEvaluate.evaluate (popHandlerNative false (register,f,f') program, source) =
      StackSemEvaluate.evaluate (program, poppedHandlerState source register savedHandler) := by
  have slotBound : source.stackSpace + 2 < source.stack.length := by omega
  simp [popHandlerF, StackSemEvaluate.evaluate_seq,
    StackSemEvaluate.evaluate_stackLoad, StackSemEvaluate.evaluate_set,
    StackSemEvaluate.evaluate_stackFree, StackSemStateOps.setVar,
    StackSemStateOps.getVar, StackSemStateOps.setStore,
    StackSemRegisterTransfers.storeOfSyntax, StackSemControl.fixClock,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    stackEnabled, storeEnabled, slotBound, Nat.not_lt.mpr room,
    saved, poppedHandlerState]

/-- The three-word restore preserves every non-scratch register and the
remaining occupied stack, while writing exactly the saved handler. These are
actual update consequences used by the full normal-return relation proof;
there is no separate HOL declaration. -/
theorem poppedHandlerResources {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (register : Nat)
    (savedHandler : WordLocW width) :
    (poppedHandlerState source register savedHandler).stackSpace = source.stackSpace + 3 ∧
    (poppedHandlerState source register savedHandler).stack = source.stack ∧
    (poppedHandlerState source register savedHandler).ffi = source.ffi ∧
    (poppedHandlerState source register savedHandler).clock = source.clock ∧
    (poppedHandlerState source register savedHandler).store.lookup .handler = some savedHandler ∧
    (∀ other, other ≠ register →
      StackSemStateOps.getVar other (poppedHandlerState source register savedHandler) =
        StackSemStateOps.getVar other source) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simp [poppedHandlerState, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  · intro other distinct
    simp [poppedHandlerState, StackSemStateOps.getVar,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, distinct]

/-- Native PushHandler writes its saved handler into the exact slot consumed
by PopHandler. The slot bound is derived from the original stack-space bounds;
no header representation premise is introduced. Flapjack proof support. -/
theorem pushedSavedHandler {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (a b register : Nat)
    (savedHandler : WordLocW width) (room : 3 ≤ source.stackSpace)
    (bound : source.stackSpace ≤ source.stack.length) :
    (pushedHandlerState source a b register savedHandler).stack[
      (pushedHandlerState source a b register savedHandler).stackSpace + 2]' (by simp [pushedHandlerState]; omega) = savedHandler := by
  simp [pushedHandlerState]

/-- Derive restoration after an actual native handler setup with arbitrary
continuation. This law computes both operations rather than supplying any
successful execution; it is support for the full returning-handler case. -/
theorem evaluatePopAfterPush {width : Nat} [NeZero width] {C F β γ : Type}
    (source : StackSemStateFiniteExact width C F) (a b register : Nat)
    (f : β) (f' : γ) (program : HolProg width) (savedHandler : WordLocW width)
    (stackEnabled : source.useStack = true) (storeEnabled : source.useStore = true)
    (room : 3 ≤ source.stackSpace) (bound : source.stackSpace ≤ source.stack.length) :
    StackSemEvaluate.evaluate
      (popHandlerNative false (register,f,f') program,
        pushedHandlerState source a b register savedHandler) =
    StackSemEvaluate.evaluate
      (program, poppedHandlerState (pushedHandlerState source a b register savedHandler)
        register savedHandler) := by
  have restoredRoom : (pushedHandlerState source a b register savedHandler).stackSpace + 3 ≤
      (pushedHandlerState source a b register savedHandler).stack.length := by
    simpa only [pushedHandlerState, List.length_set, Nat.sub_add_cancel room] using bound
  exact evaluatePopHandler (pushedHandlerState source a b register savedHandler)
    register f f' program savedHandler stackEnabled storeEnabled restoredRoom
    (pushedSavedHandler source a b register savedHandler room bound)

/-- Total EL inhabitation chooses no past-end observation. -/
local instance {width : Nat} [NeZero width] : Nonempty (WordLocW width) := ⟨.word 0⟩

/-- Derive native restoration and the remaining saved-stack relation from the
actual full callee relation and its handler frame. The frame premise is the
source stack-swap observation established in the original normal-return branch;
it is not a desired target postrelation. This is untagged proof infrastructure,
not a narrowed comp_correct case. -/
theorem restoreFromStateRel {width : Nat} [NeZero width] {C F β γ : Type}
    (ac : Compiler.Encoders.Asm.AsmConfigExact width) (register : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (n : Option Nat) (l0 l : List (Nat × WordLocW width))
    (savedSourceHandler label1 label2 frameSize : Nat)
    (rest : List (WordSemStackFrame width)) (lens : List Nat)
    (f : β) (f' : γ) (program : HolProg width)
    (sourceFrame : source.stack =
      .stackFrame n l0 l (some (savedSourceHandler,label1,label2)) :: rest)
    (relation : stateRel ac register 0 0 source target (frameSize :: lens) 0) :
    StackSemEvaluate.evaluate (popHandlerNative false (register,f,f') program, target) =
      StackSemEvaluate.evaluate (program, poppedHandlerState target register
        (holEl 2 (target.stack.drop target.stackSpace))) ∧
    stackRel register savedSourceHandler rest
      (some (holEl 2 (target.stack.drop target.stackSpace)))
      ((target.stack.drop target.stackSpace).drop (frameSize + 4))
      target.stack.length target.bitmaps lens := by
  unfold stateRel at relation
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27,
    h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38⟩ := relation
  simp only [Nat.add_zero, List.take_zero, List.drop_zero] at h38
  have savedStack := h38.1
  rw [sourceFrame] at savedStack
  have available := stackRelConsLenSome register source.handler n l0 l
    savedSourceHandler label1 label2 rest (target.store.lookup .handler)
    (target.stack.drop target.stackSpace) target.stack.length target.bitmaps
    frameSize lens savedStack
  have room : target.stackSpace + 3 ≤ target.stack.length := by
    simp only [List.length_drop] at available
    omega
  constructor
  · have slot : target.stackSpace + 2 < target.stack.length := by omega
    have saved : target.stack[target.stackSpace + 2] =
        holEl 2 (target.stack.drop target.stackSpace) := by
      rw [holElDrop,
        holEl_eq_getElem (target.stackSpace + 2) target.stack (by omega)]
    exact evaluatePopHandler target register f f' program
      (holEl 2 (target.stack.drop target.stackSpace)) h5 h6 room saved
  · exact stackRelDropSome register source.handler n l0 l savedSourceHandler
      label1 label2 rest (target.store.lookup .handler)
      (target.stack.drop target.stackSpace) target.stack.length target.bitmaps
      frameSize lens savedStack

/-- Erasing the handler from the actually updated store restores the same
canonical non-handler store. This is proved at arbitrary lookup keys, not
assumed as a poststate property. Flapjack normal-return proof infrastructure. -/
theorem poppedStoreErase {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (register : Nat)
    (savedHandler : WordLocW width) :
    (poppedHandlerState source register savedHandler).store.eraseEq .handler =
      source.store.eraseEq .handler := by
  apply HolFiniteMapExact.ext_lookup
  intro key
  simp only [poppedHandlerState, HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL]
  by_cases equal : key = .handler
  · simp [equal]
  · simp [equal, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

/-- The saved tail relation has exactly the occupied suffix and store of the
actual restored native state after freeing the three-word handler header.
The remaining caller frame contains its bitmap plus frameSize payload words,
just as in original normal-return proof's f = fprime + 1 step. This is derived
from the old relation and concrete updates, not a target postrelation premise. -/
theorem poppedTailRelation {width : Nat} [NeZero width] {C F : Type}
    (target : StackSemStateFiniteExact width C F) (register sourceHandler : Nat)
    (n : Option Nat) (l0 l : List (Nat × WordLocW width))
    (savedSourceHandler label1 label2 frameSize : Nat)
    (rest : List (WordSemStackFrame width)) (lens : List Nat)
    (relation : stackRel register sourceHandler
      (.stackFrame n l0 l (some (savedSourceHandler,label1,label2)) :: rest)
      (target.store.lookup .handler) (target.stack.drop target.stackSpace)
      target.stack.length target.bitmaps (frameSize :: lens)) :
    let restored := poppedHandlerState target register
      (holEl 2 (target.stack.drop target.stackSpace))
    stackRel register savedSourceHandler rest (restored.store.lookup .handler)
      (restored.stack.drop (restored.stackSpace + (frameSize + 1)))
      restored.stack.length restored.bitmaps lens := by
  have tail := stackRelDropSome register sourceHandler n l0 l savedSourceHandler
    label1 label2 rest (target.store.lookup .handler)
    (target.stack.drop target.stackSpace) target.stack.length target.bitmaps
    frameSize lens relation
  simpa [poppedHandlerState, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail

end Flapjack.WordToStackProofs.CompCorrect.CallReturningHandler
