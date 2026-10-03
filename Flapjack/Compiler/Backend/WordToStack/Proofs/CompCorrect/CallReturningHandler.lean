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

/-- Execute the real returning-handler header after destination and saved
frame setup, deriving its final full state relation from evaluate_PushHandler.
The initial room and label guards are the original successful header branch;
no intermediate target execution or final relation is assumed. This is
Flapjack case infrastructure, not the whole comp_correct theorem. -/
theorem evaluateHandlerHeader {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
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
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar, handlerCode, h1, h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar, handlerCode, h1, h2))) < 2 * frame + 2 * k)
    (destinationCompile : callDestNative dest args (k, f, frame) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, f, frame) =
      (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, f, frame) =
      (returnCode, (finalBitmaps, finalIndex)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend finalBitmaps).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (room : 3 ≤ target.stackSpace)
    (location : StackSem.locCheckExact target.code (h1,h2)) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate
        (.seq (.seq destinationCode savedCode) (pushHandlerNative false h1 h2 (k,f,frame)),
          target) = (none, post) ∧
      stateRel ac k 0 0
        {WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) source
          with locals := .ln, localsSize := some 0}
        post (frame :: lens) 0 ∧
      post.stackSpace + 3 = target.stackSpace ∧
      post.stack.length = target.stack.length := by
  obtain ⟨savedTarget, savedClockRun, savedRelation, _, savedLength, savedSpace⟩ :=
    evaluateHandlerPrelude ac k f frame values names retCode l1 l2 dest args
      (some (handlerVar,handlerCode,h1,h2)) source target lens xs args1 prog ss envs
      bs savedBitmaps finalBitmaps n savedIndex finalIndex destinationCode savedCode
      returnCode destination guards related conventions maximum destinationCompile
      savedCompile returnCompile lengthBound bitmapBound bitmapPrefix
  have savedRun : StackSemEvaluate.evaluate (.seq destinationCode savedCode, target) =
      (none, savedTarget) := by simpa using savedClockRun 0
  have mono := Flapjack.Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (.seq destinationCode savedCode) target savedTarget none savedRun
  have savedLocation := LocationLabels.locCheckSubset target.code savedTarget.code
    mono.2 (h1,h2) location
  obtain ⟨post, pushRun, _, _, _, postSpace, postLength, postRelation⟩ :=
    evaluatePushHandler ac k f frame h1 h2 handlerVar handlerCode source savedTarget
      envs lens (by rw [savedSpace]; exact room) savedRelation savedLocation
  refine ⟨post, ?_, postRelation, postSpace.trans savedSpace, postLength.trans savedLength⟩
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, savedRun]
  exact pushRun

/-- The real insufficient-header-room branch halts with word two and
preserves the original FFI state. This proves the target resource failure from
source-derived setup, not an assumed run; the source stack-limit consequence
and full comp_correct resource conclusion remain separate open obligations.
There is no separate HOL declaration for this case factoring. -/
theorem evaluateHandlerHeaderNoRoom {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
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
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar, handlerCode, h1, h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar, handlerCode, h1, h2))) < 2 * frame + 2 * k)
    (destinationCompile : callDestNative dest args (k, f, frame) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, f, frame) =
      (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, f, frame) =
      (returnCode, (finalBitmaps, finalIndex)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend finalBitmaps).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (noRoom : target.stackSpace < 3) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate
        (.seq (.seq destinationCode savedCode) (pushHandlerNative false h1 h2 (k,f,frame)),
          target) = (some (.halt (.word (BitVec.ofNat width 2))), post) ∧
      post.ffi = source.ffi := by
  obtain ⟨savedTarget, savedClockRun, savedRelation, _, _, savedSpace⟩ :=
    evaluateHandlerPrelude ac k f frame values names retCode l1 l2 dest args
      (some (handlerVar,handlerCode,h1,h2)) source target lens xs args1 prog ss envs
      bs savedBitmaps finalBitmaps n savedIndex finalIndex destinationCode savedCode
      returnCode destination guards related conventions maximum destinationCompile
      savedCompile returnCompile lengthBound bitmapBound bitmapPrefix
  have savedRun : StackSemEvaluate.evaluate (.seq destinationCode savedCode, target) =
      (none, savedTarget) := by simpa using savedClockRun 0
  have savedEnabled : savedTarget.useStack = true := by
    unfold stateRel at savedRelation
    aesop (config := { enableSimp := false })
  have savedFfi : savedTarget.ffi = source.ffi := by
    unfold stateRel at savedRelation
    aesop (config := { enableSimp := false })
  have short : savedTarget.stackSpace < 3 := by rw [savedSpace]; exact noRoom
  refine ⟨StackSemStateOps.emptyEnv savedTarget, ?_, ?_⟩
  · rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, savedRun]
    simp only [pushHandlerF, StackSemEvaluate.evaluate_seq,
      StackSemEvaluate.evaluate_stackAlloc,
      savedEnabled, Bool.not_true, Bool.false_eq_true, if_false, short, if_true, StackSemControl.fixClock, StackSemStateOps.emptyEnv, Nat.min_self]
  · simpa only [StackSemStateOps.emptyEnv] using savedFfi

/-- Source stack-limit overflow corresponding to insufficient room for
three handler words. The original stack_size_rel supplies the occupied size;
no source or target outcome is assumed. This is Flapjack factoring of the
resource argument at original lines9038+, not a separate HOL declaration. -/
theorem handlerNoRoomSourceLimit {width : Nat} [NeZero width] {C F α : Type}
    (source : WordSemStateFiniteExact width C F)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (args : List (WordLocW width)) (size : Option Nat)
    (frame space : Nat) (stack : List α)
    (relation : stackSizeRel frame source.localsSize source.stackLimit source.stackMax
      source.stack stack space 0)
    (positive : 0 < frame) (bound : space + frame ≤ stack.length)
    (short : space < 3) :
    source.stackLimit <
      (WordSemStateFiniteExact.callEnv args size
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          source)).stackMax.getD (source.stackLimit + 1) := by
  obtain ⟨localSize, limit, maximum⟩ := relation
  cases oldMax : source.stackMax with
  | none =>
    simp [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
      oldMax, wordSemOptionMax]
  | some old =>
    obtain ⟨_, localsSome, occupied, occupiedEq, occupiedSize⟩ := maximum old oldMax
    cases localsEq : source.localsSize with
    | none => simp [localsEq] at localsSome
    | some localCount =>
      have localFrame := localSize (by omega)
      simp only [localsEq, Option.getD_some] at localFrame
      have localsExact : source.localsSize = some frame := by
        rw [localsEq, localFrame]
      have frameSize : wordSemStackSize
          (.stackFrame source.localsSize (sptToAList envs.1)
            (wordSemEnvToList envs.2 source.permute).1 (some (source.handler,h1,h2)) ::
              source.stack) = some (3 + frame + occupied) := by
        change wordSemOptionAdd (wordSemStackSizeFrame _) (wordSemStackSize source.stack) = _
        simp only [wordSemStackSizeFrame, localsExact, Option.map_some, occupiedEq,
          wordSemOptionAdd]
      cases size with
      | none =>
        simp [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
          wordSemOptionAdd, wordSemOptionMax]
      | some size =>
        simp only [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
          frameSize, oldMax,
          wordSemOptionAdd, wordSemOptionMax, Option.getD_some]
        omega

/-- Handler-case argument-local construction after the actual three-word
header. The caller relation is retained on the pre-header state; copied
arguments are observed at the actual lowered header space. This factors the
original handler branch's local argument proof and has no separate HOL
original. The move observations are primitive register/slot facts, not an
assumed callee or post-state relation. -/
theorem handlerCalleeLocals {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize callerFrame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (saved moved : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (related : stateRel ac k callerSize callerFrame source saved lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (calleeShape : if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1)
    (argumentBound : args1.length - k ≤ calleeFrame)
    (headerSpace : Nat) (headerSpaceEq : headerSpace + 3 = saved.stackSpace)
    (space : calleeSize ≤ headerSpace)
    (registers : ∀ register, register ≠ k →
      StackSemStateOps.getVar register moved = StackSemStateOps.getVar register saved)
    (slots : ∀ index, index < args1.length - k →
      holEl (index + callerSize) (saved.stack.drop (saved.stackSpace - (args1.length - k))) =
        holEl index (moved.stack.drop (headerSpace - (args1.length - k))))
    (movedLength : moved.stack.length = saved.stack.length) :
    ∀ key value, sptLookup key (sptFromList2 args1) = some value →
      key % 2 = 0 ∧
      if key / 2 < k then (moved.regs.updateEq (0, .loc l1 l2)).lookup (key / 2) = some value
      else ((moved.stack.drop (headerSpace - calleeSize)).take calleeSize)[calleeSize - 1 - (key / 2 - k)]? = some value ∧ key / 2 < k + calleeFrame := by
  obtain ⟨get, _, find, _, _⟩ := guards
  obtain ⟨_, _, _, indirect, direct⟩ := CallTail.findCode_facts dest _
    source.code source.stackSize args1 prog ss find
  have argPrefix : args1.IsPrefix (.loc l1 l2 :: xs) := by
    cases dest with
    | none => rw [indirect rfl]; exact List.dropLast_prefix _
    | some p => rw [direct (by simp)]; exact List.prefix_refl _
  have argsEq := (CallReturning.returningConventions k values names retCode l1 l2 dest args conventions).2.1
  unfold stateRel at related
  obtain ⟨_, _, _, _, _, _, _, _, _, kPositive, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, stackBound, _, callerShape, _, _, _, locals⟩ := related
  intro key value lookup
  have index : key / 2 < args1.length := by
    rw [fromList2Lookup] at lookup
    split at lookup
    · exact (List.getElem?_eq_some_iff.mp lookup).1
    · cases lookup
  have fullLookup := lookupFromList2Prefix args1 (.loc l1 l2 :: xs) key value argPrefix lookup
  have even : key % 2 = 0 := by
    rw [fromList2Lookup] at lookup
    split at lookup
    · assumption
    · cases lookup
  refine ⟨even, ?_⟩
  by_cases zero : key = 0
  · subst key
    have valueLoc : value = .loc l1 l2 := by
      simpa [fromList2Lookup] using fullLookup.symm
    rw [if_pos (by omega), valueLoc]
    simp [FUPDATE_HOL]
  have sourceLookup := getVarsFromList2EqCons args source xs key l1 l2 value
    (by rwa [← argsEq]) fullLookup zero
  obtain ⟨_, callerLocal⟩ := locals key value sourceLookup
  by_cases inRegister : key / 2 < k
  · rw [if_pos inRegister] at callerLocal ⊢
    have preserved := registers (key / 2) (by omega)
    simp only [StackSemStateOps.getVar] at preserved
    simp only [HolFiniteMapExact.updateEq, FUPDATE_HOL]
    rw [if_neg (by omega), preserved]
    exact callerLocal
  · rw [if_neg inRegister] at callerLocal ⊢
    obtain ⟨callerSlot, callerIndex⟩ := callerLocal
    rw [if_neg (by omega)] at callerShape
    have calleePositive : 0 < calleeFrame := by omega
    rw [if_neg (by omega)] at calleeShape
    have countSpace : args1.length - k ≤ headerSpace := by omega
    have copyIndex : args1.length - k - 1 - (key / 2 - k) < args1.length - k := by omega
    have copied := slots _ copyIndex
    have callerAbsolute : saved.stackSpace + (callerSize - 1 - (key / 2 - k)) < saved.stack.length := by
      rw [Nat.add_zero, List.getElem?_take, List.getElem?_drop] at callerSlot
      split at callerSlot
      · exact (List.getElem?_eq_some_iff.mp callerSlot).1
      · cases callerSlot
    have movedAbsolute : headerSpace - calleeSize +
        (calleeSize - 1 - (key / 2 - k)) < moved.stack.length := by omega
    refine ⟨?_, by omega⟩
    rw [List.getElem?_take, if_pos (by omega), List.getElem?_drop,
      List.getElem?_eq_getElem movedAbsolute]
    rw [Nat.add_zero, List.getElem?_take, if_pos (by omega), List.getElem?_drop,
      List.getElem?_eq_getElem callerAbsolute] at callerSlot
    rw [holEl_eq_getElem _ _ (by simp; omega), holEl_eq_getElem _ _ (by simp; omega),
      List.getElem_drop, List.getElem_drop] at copied
    have sourceIndex : saved.stackSpace - (args1.length - k) +
        (args1.length - k - 1 - (key / 2 - k) + callerSize) =
        saved.stackSpace + (callerSize - 1 - (key / 2 - k)) := by omega
    have targetIndex : headerSpace - (args1.length - k) +
        (args1.length - k - 1 - (key / 2 - k)) =
        headerSpace - calleeSize + (calleeSize - 1 - (key / 2 - k)) := by omega
    simp only [sourceIndex, targetIndex] at copied
    rw [← copied]
    exact callerSlot

/-- Execute the real handler argument allocation/move and connect its
slots to the pre-header caller stack. Header writes lie below the occupied
caller slots. This supports the original handler callee entry; the target
move and its register/slot observations are proved, not supplied. There is
no separate HOL declaration for this case-local composition. -/
theorem evaluateHandlerArguments {width : Nat} [NeZero width] {C F : Type}
    (k f frame h1 h2 : Nat) (destination : Sum Nat Nat) (argCount : Nat)
    (saved : StackSemStateFiniteExact width C F) (savedHandler : WordLocW width)
    (useStack : saved.useStack = true) (room : 3 ≤ saved.stackSpace)
    (frameBound : saved.stackSpace + f ≤ saved.stack.length)
    (moveBound : Compiler.Backend.WordToStack.stackArgCount destination argCount k ≤ f)
    (space : Compiler.Backend.WordToStack.stackArgCount destination argCount k ≤
      (pushedHandlerState saved h1 h2 k savedHandler).stackSpace) :
    let count := Compiler.Backend.WordToStack.stackArgCount destination argCount k
    let header := pushedHandlerState saved h1 h2 k savedHandler
    ∃ (moved : StackSemStateFiniteExact width C F) (stack : List (WordLocW width))
      (regs : HolFiniteMapExact Nat (WordLocW width)),
      StackSemEvaluate.evaluate
        (stackHandlerArgsNative false destination argCount (k,f,frame), header) =
          (none, moved) ∧
      moved = {header with stackSpace := header.stackSpace-count, stack := stack, regs := regs} ∧
      (∀ register, register ≠ k → StackSemStateOps.getVar register moved =
        StackSemStateOps.getVar register saved) ∧
      moved.stack.length = saved.stack.length ∧
      moved.stackSpace = header.stackSpace - count ∧
      moved.stack.drop (moved.stackSpace + count) = header.stack.drop header.stackSpace ∧
      (∀ index, index < count →
        holEl (index + f) (saved.stack.drop (saved.stackSpace - count)) =
          holEl index (moved.stack.drop (header.stackSpace - count))) := by
  dsimp only
  let header := pushedHandlerState saved h1 h2 k savedHandler
  let count := Compiler.Backend.WordToStack.stackArgCount destination argCount k
  have resources := pushedHandlerStateResources saved h1 h2 k savedHandler room
  have headerLength : header.stack.length = saved.stack.length := resources.2.2
  have headerSpace : header.stackSpace + 3 = saved.stackSpace := resources.2.1
  obtain ⟨moved, stack, regs, run, movedState, registers, stackLength, movedSpace, tail, slots⟩ :=
    CallReturning.evaluateStackArguments k (f+3) (frame+3) destination argCount header
      useStack (by rw [headerLength]; omega)
      (by omega) space
  refine ⟨moved, stack, regs, ?_, movedState, ?_, ?_, movedSpace, ?_, ?_⟩
  · rw [stackHandlerArgsF]
    exact run
  · intro register distinct
    exact (registers register distinct).trans (resources.1 register distinct)
  · rw [movedState]
    change stack.length = saved.stack.length
    exact stackLength.symm.trans resources.2.2
  · simpa only [movedState] using tail
  · intro index indexBound
    have copied := slots index indexBound
    change holEl (index + (f+3)) (header.stack.drop (header.stackSpace - count)) =
      holEl index (stack.drop (header.stackSpace - count)) at copied
    rw [movedState]
    change holEl (index+f) (saved.stack.drop (saved.stackSpace-count)) =
      holEl index (stack.drop (header.stackSpace-count))
    rw [← copied, holElDrop, holElDrop]
    have absoluteEq : header.stackSpace-count+(index+(f+3)) =
        saved.stackSpace-count+(index+f) := by
      change saved.stackSpace-3-count+(index+(f+3)) = _
      omega
    rw [absoluteEq]
    have unchanged := congrArg (holEl (index+f-count))
      (pushedHandlerStateOccupiedSuffix saved h1 h2 k savedHandler room)
    rw [holElDrop, holElDrop] at unchanged
    have sameIndex : saved.stackSpace+(index+f-count) =
        saved.stackSpace-count+(index+f) := by omega
    rw [sameIndex] at unchanged
    exact unchanged.symm

/-- Full handler callee-entry state relation from the actual saved frame,
three-word PushHandler update and argument-move observations. The handler
frame is decoded by the already checked PushHandler relation; the local
argument conjunct uses the original pre-header caller. Every callee state
field is proved. This is Flapjack case infrastructure, not a whole
comp_correct port or an assumption of its target execution/result. -/
theorem handlerCalleeStateRel {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize callerFrame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (savedHandler : WordLocW width)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (saved header : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (stack : List (WordLocW width)) (regs : HolFiniteMapExact Nat (WordLocW width))
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize callerFrame source saved lens 0)
    (prePushRelation : stateRel ac k 0 0
      {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
      saved (callerFrame :: lens) 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) = true)
    (headerState : header = pushedHandlerState saved h1 h2 k savedHandler)
    (savedLookup : saved.store.lookup .handler = some savedHandler)
    (room : 3 ≤ saved.stackSpace)
    (calleeShape : if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1)
    (calleeLocalsSize : ss.getD calleeSize = calleeSize)
    (argumentBound : args1.length - k ≤ calleeFrame)
    (space : calleeSize ≤ header.stackSpace)
    (registers : ∀ register, register ≠ k → regs.lookup register = saved.regs.lookup register)
    (slots : ∀ index, index < args1.length - k →
      holEl (index + callerSize) (saved.stack.drop (saved.stackSpace - (args1.length - k))) =
        holEl index (stack.drop (header.stackSpace - (args1.length - k))))
    (stackLength : stack.length = saved.stack.length)
    (stackTail : stack.drop header.stackSpace = header.stack.drop header.stackSpace) :
    stateRel ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source)))
      {header with
        clock := header.clock - 1, stackSpace := header.stackSpace - calleeSize,
        stack := stack, regs := regs.updateEq (0, .loc l1 l2)}
      (callerFrame :: lens) 0 := by
  have pushedRelation := stateRelPushedHandler ac k callerFrame h1 h2 handlerVar handlerCode
    source saved envs lens savedHandler savedLookup room prePushRelation
  rw [← headerState] at pushedRelation
  have resources := pushedHandlerStateResources saved h1 h2 k savedHandler room
  have headerLength : header.stack.length = saved.stack.length := by
    rw [headerState]; exact resources.2.2
  have headerSpace : header.stackSpace + 3 = saved.stackSpace := by
    rw [headerState]; exact resources.2.1
  have actualLength : stack.length = header.stack.length := stackLength.trans headerLength.symm
  have plainConventions := conventionsWithoutHandler k values names retCode l1 l2 dest args
    (some (handlerVar,handlerCode,h1,h2)) conventions
  let cleared := {WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) source with
    locals := .ln, localsSize := some 0}
  have calleeSource : WordSemStateFiniteExact.callEnv args1 ss
      (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source)) =
      WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.decClock cleared) := by
    rfl
  rw [calleeSource]
  change stateRel ac k 0 0 cleared header (callerFrame :: lens) 0 at pushedRelation
  unfold stateRel at pushedRelation
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18,
    g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, _, _,
    resource, oldStack, _⟩ := pushedRelation
  unfold stateRel
  refine ⟨?_, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18,
    g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, ?_, ?_,
    calleeShape, wfFromList2 args1, ?_, ?_, ?_⟩
  · show cleared.clock - 1 = header.clock - 1
    rw [g1]
  · show header.stackSpace - calleeSize + calleeSize ≤ stack.length
    omega
  · show stack.length < 2 ^ width
    omega
  · change stackSizeRel calleeSize ss cleared.stackLimit
      (wordSemOptionMax cleared.stackMax (wordSemOptionAdd (wordSemStackSize cleared.stack) ss))
      cleared.stack stack (header.stackSpace - calleeSize) 0
    obtain ⟨_, limit, maximum⟩ := resource
    refine ⟨fun _ => calleeLocalsSize, by simpa only [actualLength] using limit, ?_⟩
    intro newMaximum newValue
    rcases oldValue : cleared.stackMax with _ | oldMaximum
    · rw [oldValue] at newValue
      simp [wordSemOptionMax] at newValue
    obtain ⟨oldBound, _, size, oldSize, sizeValue⟩ := maximum oldMaximum oldValue
    rcases sizeOption : ss with _ | size
    · rw [oldValue, sizeOption, oldSize] at newValue
      simp [wordSemOptionMax, wordSemOptionAdd] at newValue
    rw [sizeOption] at calleeLocalsSize
    simp only [Option.getD_some] at calleeLocalsSize
    subst size
    rw [oldValue, oldSize, sizeOption] at newValue
    simp only [wordSemOptionMax, wordSemOptionAdd, Option.some.injEq] at newValue
    have := Nat.le_max_right oldMaximum (size + calleeSize)
    refine ⟨by omega, by simp, size, oldSize, by omega⟩
  · change stackRel k cleared.handler cleared.stack (header.store.lookup .handler)
      ((stack.drop (header.stackSpace - calleeSize + 0)).drop calleeSize)
      stack.length header.bitmaps (callerFrame :: lens)
    rw [List.drop_drop, Nat.add_zero, Nat.sub_add_cancel space, stackTail, actualLength]
    simpa only [Nat.add_zero, Nat.add_zero, List.drop_zero] using oldStack
  · apply handlerCalleeLocals ac k callerSize callerFrame calleeSize calleeFrame values names
      retCode l1 l2 dest args source saved {header with stack := stack, regs := regs} lens
      xs args1 prog ss envs guards callerRelation plainConventions calleeShape argumentBound
      header.stackSpace headerSpace space
    · intro register distinct
      change regs.lookup register = saved.regs.lookup register
      exact registers register distinct
    · exact slots
    · exact stackLength

/-- Actual StackHandlerArgs execution and native callee frame allocation,
with the full original handler callee-entry relation. The pushed header is
an explicit actual update of the saved caller, and all argument observations
are derived by executing the native move. This is Flapjack case factoring,
not the whole comp_correct result or an assumed callee target run. -/
theorem enterHandlerCallee {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize callerFrame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (savedHandler : WordLocW width)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (saved : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (destinationCode : HolProg width) (destination : Sum Nat Nat)
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize callerFrame source saved lens 0)
    (prePushRelation : stateRel ac k 0 0
      {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
      saved (callerFrame :: lens) 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) < 2 * callerFrame + 2 * k)
    (destinationCompile : callDestNative dest args (k, callerSize, callerFrame) =
      (destinationCode, destination))
    (savedLookup : saved.store.lookup .handler = some savedHandler)
    (room : 3 ≤ saved.stackSpace)
    (calleeShape : if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1)
    (calleeLocalsSize : ss.getD calleeSize = calleeSize)
    (argumentBound : args1.length - k ≤ calleeFrame)
    (space : calleeSize ≤ (pushedHandlerState saved h1 h2 k savedHandler).stackSpace) :
    let header := pushedHandlerState saved h1 h2 k savedHandler
    ∃ (moved entry : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (stackHandlerArgsNative false destination (args.length+1)
        (k,callerSize,callerFrame), header) = (none,moved) ∧
      StackSemEvaluate.evaluate (.stackAlloc (calleeSize-(args1.length-k)),
        StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)) =
          (none,entry) ∧
      stateRel ac k calleeSize calleeFrame
        (WordSemStateFiniteExact.callEnv args1 ss
          (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
            (WordSemStateFiniteExact.decClock source))) entry (callerFrame :: lens) 0 := by
  dsimp only
  let header := pushedHandlerState saved h1 h2 k savedHandler
  change calleeSize ≤ header.stackSpace at space
  have plainConventions := conventionsWithoutHandler k values names retCode l1 l2 dest args
    (some (handlerVar,handlerCode,h1,h2)) conventions
  have plainMaximum := lt_of_le_of_lt
    (maximumWithoutHandler values names retCode l1 l2 dest args
      (some (handlerVar,handlerCode,h1,h2))) maximum
  have countEq := CallReturning.stackArgumentCount values names retCode l1 l2 dest args
    source xs args1 prog ss envs k callerSize callerFrame destinationCode destination guards
    destinationCompile
  have countCaller := CallReturning.stackArgumentFrameBound ac k callerSize callerFrame
    values names retCode l1 l2 dest args source saved lens xs args1 prog ss envs
    destinationCode destination guards callerRelation plainConventions plainMaximum destinationCompile
  have countCallee : args1.length-k ≤ calleeSize := by
    split_ifs at calleeShape <;> omega
  have useStack : saved.useStack = true := by
    unfold stateRel at callerRelation
    aesop (config := { enableSimp := false })
  have stackBound : saved.stackSpace+callerSize ≤ saved.stack.length := by
    unfold stateRel at callerRelation
    aesop (config := { enableSimp := false })
  obtain ⟨moved, stack, regs, moveRun, movedState, registers, stackLength, movedSpace,
    tail, slots⟩ := evaluateHandlerArguments k callerSize callerFrame h1 h2 destination
      (args.length+1) saved savedHandler useStack room stackBound countCaller
      (by change Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤
            header.stackSpace; omega)
  rw [countEq] at movedState movedSpace tail slots
  subst moved
  let entry : StackSemStateFiniteExact width C F := {header with
    clock := header.clock-1, stackSpace := header.stackSpace-calleeSize,
    stack := stack, regs := regs.updateEq (0,.loc l1 l2)}
  refine ⟨_,entry,moveRun,?_,?_⟩
  · rw [StackSemEvaluate.evaluate_stackAlloc,
      if_neg (by simp [StackSemStateOps.setVar, StackSemStateOps.decClock,
        pushedHandlerState, useStack]),
      if_neg (by
        change ¬ header.stackSpace-(args1.length-k) < calleeSize-(args1.length-k)
        omega)]
    simp only [StackSemStateOps.setVar, StackSemStateOps.decClock]
    have spaceEq : header.stackSpace-(args1.length-k)-(calleeSize-(args1.length-k)) =
        header.stackSpace-calleeSize := by omega
    rw [spaceEq]
  · apply handlerCalleeStateRel ac k callerSize callerFrame calleeSize calleeFrame values names
      retCode l1 l2 dest args handlerVar h1 h2 handlerCode savedHandler source saved header
      lens xs args1 prog ss envs stack regs guards callerRelation prePushRelation conventions
      rfl savedLookup room calleeShape calleeLocalsSize argumentBound space
    · intro register distinct
      have preserved := registers register distinct
      change regs.lookup register = saved.regs.lookup register at preserved
      exact preserved
    · exact slots
    · change stack.length = saved.stack.length at stackLength
      exact stackLength
    · change stack.drop (header.stackSpace-(args1.length-k)+(args1.length-k)) =
        header.stack.drop header.stackSpace at tail
      rw [Nat.sub_add_cancel (show args1.length-k ≤ header.stackSpace by omega)] at tail
      exact tail

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
