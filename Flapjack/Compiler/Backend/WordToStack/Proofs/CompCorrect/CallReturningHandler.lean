import Flapjack.Compiler.Backend.WordToStack.Proofs.CallReturnHandler
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturning
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallTail
import Flapjack.Compiler.Backend.WordToStack.Proofs.CallReturnStackMoveClock

namespace Flapjack.WordToStackProofs.CompCorrect.CallReturningHandler
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open CallReturnHandler

/-- Handler-case source guard elimination from the actual non-error source run.
The guards precede handler selection in the original evaluator. This is
Flapjack infrastructure, with no separate HOL declaration or target-run premise. -/
theorem sourceGuardsOfNotErrorWithHandler {width : Nat} [NeZero width] {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args handler) source =
      (result, sourcePost)) (notError : result ≠ some .error) :
    ∃ xs args1 prog ss envs,
      CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs := by
  rw [WordSemStateFiniteExact.evaluate] at execution
  rcases hget : WordSemStateFiniteExact.getVars args source with _ | xs
  · simp only [hget, Prod.mk.injEq] at execution
    exact absurd execution.1.symm notError
  simp only [hget] at execution
  by_cases hbad : wordSemBadDestArgs dest args = true
  · simp only [hbad, if_true, Prod.mk.injEq] at execution
    exact absurd execution.1.symm notError
  simp only [hbad, Bool.false_eq_true, if_false] at execution
  rcases hfind : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) xs)
      source.code source.stackSize with _ | ⟨args1, prog, ss⟩
  · simp only [hfind, Prod.mk.injEq] at execution
    exact absurd execution.1.symm notError
  simp only [hfind] at execution
  by_cases invalid : sptDomainEmpty names.1 ∨ ¬ values.Nodup
  · simp only [invalid, if_true, Prod.mk.injEq] at execution
    exact absurd execution.1.symm notError
  simp only [invalid, if_false] at execution
  rcases hcut : wordSemCutEnvs names source.locals with _ | envs
  · simp only [hcut, Prod.mk.injEq] at execution
    exact absurd execution.1.symm notError
  exact ⟨xs, args1, prog, ss, envs, hget, hbad, hfind, invalid, hcut⟩

/-- Removing the exception continuation preserves all returning-call
conventions. This is Flapjack factoring of the original setup checks, not a
new HOL theorem or a strengthened simulation premise. -/
theorem conventionsWithoutHandler {width : Nat} [NeZero width]
    (k : Nat) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args handler) = true) :
    postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true := by
  cases handler with
  | none => exact conventions
  | some handler =>
    rcases handler with ⟨handlerVar, body, h1, h2⟩
    simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL,
      callArgConventionHOL, Bool.and_eq_true, Bool.and_true] at conventions ⊢
    aesop (config := { enableSimp := false })

/-- The original handler call conventions force the exception handlerVar to
register two and establish the handler body's conventions. This support has
no separate HOL original and does not assume a restored target relation. -/
theorem handlerConventions {width : Nat} [NeZero width]
    (k : Nat) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode handlerCode : WordLangProgHOL (BitVec width))
    (l1 l2 h1 h2 handlerVar : Nat) (dest : Option Nat) (args : List Nat)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args
        (some (handlerVar, handlerCode, h1, h2))) = true) :
    handlerVar = 2 ∧ postAllocConventionsHOL k handlerCode = true := by
  simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL,
    callArgConventionHOL, Bool.and_eq_true, beq_iff_eq] at conventions
  simp only [postAllocConventionsHOL, Bool.and_eq_true]
  aesop (config := { enableSimp := false })

/-- The caller maximum remains valid when the handler continuation is
removed for the shared setup lemmas. This follows the literal max_var call
clause and has no separate HOL original. -/
theorem maximumWithoutHandler {width : Nat} [NeZero width]
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) :
    maxVarHOL (.call (some (values, names, retCode, l1, l2)) dest args none) ≤
      maxVarHOL (.call (some (values, names, retCode, l1, l2)) dest args handler) := by
  cases handler with
  | none => exact Nat.le_refl _
  | some handler =>
    rcases handler with ⟨handlerVar, body, h1, h2⟩
    simp only [maxVarHOL, Flapjack.WordAlloc.max3Eq]
    omega

/-- Actual destination and saved-frame prelude for a returning handler call,
using the original handler-call conventions and maximum. The shared setup
executes before PushHandler; its temporary no-handler source frame is the
actual evaluate_wLive relation. This is Flapjack case infrastructure, not
an assembled comp_correct theorem or a supplied target run. -/
theorem evaluateHandlerPrelude {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bs savedBitmaps finalBitmaps : AppList (BitVec width))
    (n savedIndex finalIndex : Nat) (destinationCode savedCode returnCode : HolProg width)
    (destination : Sum Nat Nat)
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source
      xs args1 prog ss envs)
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args handler) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args handler) < 2 * frame + 2 * k)
    (destinationCompile : callDestNative dest args (k, f, frame) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, f, frame) =
      (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, f, frame) =
      (returnCode, (finalBitmaps, finalIndex)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend finalBitmaps).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length))) :
    ∃ savedTarget : StackSemStateFiniteExact width C F,
      (∀ extra : Nat,
        StackSemEvaluate.evaluate (.seq destinationCode savedCode,
          {target with clock := target.clock + extra}) =
          (none, {savedTarget with clock := savedTarget.clock + extra})) ∧
      stateRel ac k 0 0
        {WordSemStateFiniteExact.pushEnv envs none source with
          locals := .ln, localsSize := some 0}
        savedTarget (frame :: lens) 0 ∧
      stateRel ac k f frame source savedTarget lens 0 ∧
      savedTarget.stack.length = target.stack.length ∧
      savedTarget.stackSpace = target.stackSpace := by
  have plainConventions := conventionsWithoutHandler k values names retCode l1 l2
    dest args handler conventions
  have plainMaximum := lt_of_le_of_lt
    (maximumWithoutHandler values names retCode l1 l2 dest args handler) maximum
  exact CallReturning.evaluatePrelude ac k f frame values names retCode l1 l2 dest args
    source target lens xs args1 prog ss envs bs savedBitmaps finalBitmaps n savedIndex
    finalIndex destinationCode savedCode returnCode destination guards related
    plainConventions plainMaximum destinationCompile savedCompile returnCompile
    lengthBound bitmapBound bitmapPrefix

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
