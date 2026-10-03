import Flapjack.Compiler.Backend.WordToStack.Proofs.HandlerTransition
import Flapjack.FiniteMap.MapKeys
import Flapjack.Compiler.Backend.WordToStack.NativeHandlers
import Flapjack.Compiler.Backend.WordToStack.Proofs.CallReturnEval
import Flapjack.Compiler.Backend.WordToStack.Proofs.CallReturnSupport
import Flapjack.Compiler.Backend.StackProps.EvaluateAddClock

namespace Flapjack.WordToStackProofs.CallReturnHandler
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native CallReturnEval

/-- Original non-performance argument frame, with arbitrary destination carriers. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "StackHandlerArgs_F"
  (words_as_type_indexed_bitvec)]
theorem stackHandlerArgsF {width : Nat} [NeZero width] {α β : Type}
    (dest : Sum α β) (argCount k f f' : Nat) :
    (stackHandlerArgsNative false dest argCount (k, f, f') : HolProg width) =
      stackArgsNative dest argCount (k, f + 3, f' + 3) := rfl

/-- Original non-performance handler save tree. Unused frame carriers remain
independent, as in the native HOL definition. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "PushHandler_F"
  (words_as_type_indexed_bitvec)]
theorem pushHandlerF {width : Nat} [NeZero width] {β γ : Type}
    (l1 l2 k : Nat) (f : β) (f' : γ) :
    (pushHandlerNative false l1 l2 (k, f, f') : HolProg width) =
      .seq (.stackAlloc 3)
        (.seq (.inst (.const k (1 : BitVec width)))
          (.seq (.stackStore k 0)
            (.seq (.locValue k l1 l2)
              (.seq (.stackStore k 1)
                (.seq (.get k .handler)
                  (.seq (.stackStore k 2)
                    (.seq .skip (.seq (.stackGetSize k) (.set .handler k))))))))) := rfl

/-- Original restoration/free tree with arbitrary continuation and independent
unused frame carriers. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "PopHandler_F"
  (words_as_type_indexed_bitvec)]
theorem popHandlerF {width : Nat} [NeZero width] {β γ : Type}
    (k : Nat) (f : β) (f' : γ) (program : HolProg width) :
    popHandlerNative false (k, f, f') program =
      .seq (.stackLoad k 2) (.seq (.set .handler k) (.seq (.stackFree 3) program)) := rfl

/-- The actual imported state owner's checked codec, re-exported for the
representation qualifier. No separate HOL declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Weaken the reviewed constructor clock law to the peer composition law.
Flapjack infrastructure, without a separate HOL original. -/
private theorem clockFreeCtor {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width)
    (free : Compiler.Backend.StackProps.EvaluateAddClock.clockFreeCtor program = true) :
    ClockFree (C := C) (F := F) program := by
  intro source clock
  exact (Compiler.Backend.StackProps.EvaluateAddClock.clockFree_of_ctor program free source clock).1

/-- Full original unconditional clock replacement law for PushHandler F.
All source error/success branches and arbitrary clocks are retained. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_PushHandler_clock"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluatePushHandlerClock {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (a b k f f' clock : Nat) :
    StackSemEvaluate.evaluate (pushHandlerNative false a b (k, f, f'),
      {source with clock := clock}) =
      ((StackSemEvaluate.evaluate (pushHandlerNative false a b (k, f, f'), source)).1,
        {(StackSemEvaluate.evaluate (pushHandlerNative false a b (k, f, f'), source)).2
          with clock := clock}) := by
  suffices free : ClockFree (C := C) (F := F) (pushHandlerNative false a b (k, f, f')) from
    free source clock
  rw [pushHandlerF]
  repeat' first
    | apply clockFree_seq
    | exact clockFree_const _ _
    | exact clockFreeCtor _ rfl

/-- Inhabitation only for total HOL EL; no out-of-range value is selected. -/
local instance {width : Nat} [NeZero width] : Nonempty (WordLocW width) :=
  ⟨.word 0⟩
local instance {width : Nat} [NeZero width] : Nonempty (WordSemStackFrame width) :=
  ⟨.stackFrame none [] [] none⟩

/-- Extract the actual four-word handler header and payload from successful
native decoding. Flapjack infrastructure with no separate HOL original. -/
theorem absStackConsSome {width frameWidth : Nat} [NeZero width] [NeZero frameWidth]
    (bs : List (BitVec width)) (n : Option Nat) (l0 l : List (Nat × WordLocW frameWidth))
    (saved : Nat × Nat × Nat) (wstack : List (WordSemStackFrame frameWidth))
    (sstack : List (WordLocW width)) (f' : Nat) (lens : List Nat)
    (astack : List (Option (WordLocW width × WordLocW width) × List Bool × List (WordLocW width)))
    (decoded : absStack bs (.stackFrame n l0 l (some saved) :: wstack) sstack (f' :: lens) =
      some astack) :
    ∃ loc hv bitmap rest bits ys,
      sstack = .word 1 :: loc :: hv :: bitmap :: rest ∧
      StackSem.fullReadBitmap bs bitmap = some bits ∧
      bits.length = f' ∧ f' ≤ rest.length ∧
      absStack bs wstack (rest.drop f') lens = some ys ∧
      astack = (some (loc, hv), bits, rest.take f') :: ys := by
  rcases sstack with _ | ⟨marker, stack⟩
  · rw [absStack.eq_def] at decoded; simp at decoded
  rw [absStack.eq_def] at decoded
  simp only at decoded
  split at decoded
  · simp at decoded
  rename_i markerEq
  have markerOne : marker = .word 1 := by simpa using markerEq
  subst marker
  rcases stack with _ | ⟨loc, _ | ⟨hv, _ | ⟨bitmap, rest⟩⟩⟩ <;>
    simp only [reduceCtorEq] at decoded
  rcases read : StackSem.fullReadBitmap bs bitmap with _ | bits
  · simp [read] at decoded
  simp only [read] at decoded
  split at decoded
  · simp at decoded
  split at decoded
  · simp at decoded
  rename_i lengthEq bound
  rcases recurse : absStack bs wstack (rest.drop f') lens with _ | ys
  · simp [recurse] at decoded
  simp only [recurse, Option.some.injEq] at decoded
  exact ⟨loc, hv, bitmap, rest, bits, ys, rfl, read,
    by simpa using lengthEq, by omega, recurse, decoded.symm⟩

/-- Full original handler-frame length law, with its sole stack relation premise. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_rel_cons_LEN_SOME"
  (words_as_type_indexed_bitvec)]
theorem stackRelConsLenSome {width : Nat} {handlerWidth : Nat} [NeZero width] [NeZero handlerWidth]
    (k whandler : Nat) (n : Option Nat) (l0 l : List (Nat × WordLocW width))
    (a b c : Nat) (wstack : List (WordSemStackFrame width))
    (shandler : Option (WordLocW handlerWidth)) (sstack : List (WordLocW width))
    (len : Nat) (bs : List (BitVec width)) (f' : Nat) (lens : List Nat)
    (relation : stackRel k whandler (.stackFrame n l0 l (some (a,b,c)) :: wstack)
      shandler sstack len bs (f' :: lens)) : f' + 4 ≤ sstack.length := by
  obtain ⟨_, astack, decoded, _, _⟩ := relation
  obtain ⟨loc, hv, bitmap, rest, bits, ys, rfl, _, _, bound, _, _⟩ :=
    absStackConsSome bs n l0 l (a,b,c) wstack sstack f' lens astack decoded
  simp only [List.length_cons]
  omega

/-- Full original handler-frame removal law: the saved handler is read from
actual total EL 2, and the tail relation is derived, never assumed. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_rel_DROP_SOME"
  (words_as_type_indexed_bitvec)]
theorem stackRelDropSome {width : Nat} {handlerWidth : Nat} [NeZero width] [NeZero handlerWidth]
    (k whandler : Nat) (n : Option Nat) (l0 l : List (Nat × WordLocW width))
    (whandler' b c : Nat) (wstack : List (WordSemStackFrame width))
    (shandler : Option (WordLocW handlerWidth)) (sstack : List (WordLocW width))
    (len : Nat) (bs : List (BitVec width)) (f' : Nat) (lens : List Nat)
    (relation : stackRel k whandler (.stackFrame n l0 l (some (whandler',b,c)) :: wstack)
      shandler sstack len bs (f' :: lens)) :
    stackRel k whandler' wstack (some (holEl 2 sstack)) (sstack.drop (f' + 4)) len bs lens := by
  obtain ⟨sorted, astack, decoded, _, auxiliary⟩ := relation
  obtain ⟨loc, hv, bitmap, rest, bits, ys, rfl, _, _, _, recurse, rfl⟩ :=
    absStackConsSome bs n l0 l (whandler',b,c) wstack sstack f' lens astack decoded
  have lengths : ys.length = wstack.length := (absStackImpLength _ _ _ _ _ recurse).1
  simp only [stackRelAux] at auxiliary
  refine ⟨?_, ys, ?_, ?_, auxiliary.2.2.2.2.2⟩
  · simp only [List.all_cons, Bool.and_eq_true] at sorted
    exact sorted.2
  · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using recurse
  · intro bound active
    have saved := auxiliary.1 (by omega) (by simpa only [lengths] using active)
    change some hv = _
    simpa only [lengths] using congrArg some saved

/-- Concrete state produced by the original non-performance handler setup.
This Flapjack helper names actual updates; it is not a replacement evaluator. -/
def pushedHandlerState {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (a b register : Nat)
    (savedHandler : WordLocW width) : StackSemStateFiniteExact width C F :=
  let space := source.stackSpace - 3
  {source with
    stackSpace := space,
    regs := source.regs.updateEq (register, .word (BitVec.ofNat width space)),
    stack := ((source.stack.set space (.word 1)).set (space + 1) (.loc a b)).set
      (space + 2) savedHandler,
    store := source.store.updateEq (.handler, .word (BitVec.ofNat width space))}

/-- Actual native setup execution from its primitive guards, used to prove the
full state-relation transition. No target evaluation or postrelation is supplied;
this is untagged infrastructure, not the full HOL evaluate_PushHandler port. -/
theorem evaluatePushHandlerUpdates {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (a b register f f' : Nat)
    (savedHandler : WordLocW width)
    (stackEnabled : source.useStack = true) (storeEnabled : source.useStore = true)
    (room : 3 ≤ source.stackSpace) (stackBound : source.stackSpace ≤ source.stack.length)
    (saved : source.store.lookup .handler = some savedHandler)
    (location : StackSem.locCheckExact source.code (a,b)) :
    StackSemEvaluate.evaluate (pushHandlerNative false a b (register,f,f'), source) =
      (none, pushedHandlerState source a b register savedHandler) := by
  have firstBound : source.stackSpace - 3 < source.stack.length := by omega
  have secondBound : source.stackSpace - 3 + 1 < source.stack.length := by omega
  have thirdBound : source.stackSpace - 3 + 2 < source.stack.length := by omega
  simp [pushHandlerF, StackSemEvaluate.evaluate_seq,
    StackSemEvaluate.evaluate_stackAlloc, StackSemEvaluate.evaluate_inst,
    StackSemEvaluate.evaluate_stackStore, StackSemEvaluate.evaluate_locValue,
    StackSemEvaluate.evaluate_get, StackSemEvaluate.evaluate_skip,
    StackSemEvaluate.evaluate_stackGetSize, StackSemEvaluate.evaluate_set,
    StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    StackSemExpressions.assign, StackSemExpressions.wordExp,
    StackSemStateOps.setVar, StackSemStateOps.getVar, StackSemStateOps.setStore,
    StackSemRegisterTransfers.storeOfSyntax,
    StackSemControl.fixClock, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, stackEnabled, storeEnabled,
    Nat.not_lt.mpr room, Nat.not_le.mpr firstBound, Nat.not_le.mpr secondBound,
    Nat.not_le.mpr thirdBound, saved, location, pushedHandlerState]
  apply HolFiniteMapExact.ext_lookup
  intro key
  by_cases equal : key = register <;>
    simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, equal]

/-- Derive all primitive execution guards from the original initial relation.
This is supporting infrastructure; the full final relation is still a separate
obligation of evaluate_PushHandler, not an added premise. -/
theorem evaluatePushHandlerFromStateRel {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (register f f' a b : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (envs : Spt (WordLocW width) × Spt (WordLocW width)) (lens : List Nat)
    (room : 3 ≤ target.stackSpace)
    (relation : stateRel ac register 0 0
      {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
      target (f' :: lens) 0)
    (location : StackSem.locCheckExact target.code (a,b)) :
    ∃ savedHandler,
      target.store.lookup .handler = some savedHandler ∧
      StackSemEvaluate.evaluate (pushHandlerNative false a b (register,f,f'), target) =
        (none, pushedHandlerState target a b register savedHandler) := by
  unfold stateRel at relation
  obtain ⟨_, _, _, _, stackEnabled, storeEnabled, _, _, _, _, _, _, _, _, _, _, handlerPresent, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, stackBound, _⟩ := relation
  cases saved : target.store.lookup .handler with
  | none => exact False.elim (handlerPresent saved)
  | some value =>
    refine ⟨value, rfl, ?_⟩
    exact evaluatePushHandlerUpdates target a b register f f' value
      stackEnabled storeEnabled room (by simpa using stackBound) saved location

/-- Actual update preservation of unrelated registers and stack resources.
Flapjack infrastructure for the original transition's unchanged-field clauses. -/
theorem pushedHandlerStateResources {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (a b register : Nat)
    (savedHandler : WordLocW width) (room : 3 ≤ source.stackSpace) :
    (∀ index, index ≠ register →
      StackSemStateOps.getVar index (pushedHandlerState source a b register savedHandler) =
        StackSemStateOps.getVar index source) ∧
    (pushedHandlerState source a b register savedHandler).stackSpace + 3 = source.stackSpace ∧
    (pushedHandlerState source a b register savedHandler).stack.length = source.stack.length := by
  refine ⟨?_, ?_, ?_⟩
  · intro index distinct
    simp [pushedHandlerState, StackSemStateOps.getVar,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, distinct]
  · simp only [pushedHandlerState]
    omega
  · simp [pushedHandlerState]

/-- The three actual header writes leave the original occupied suffix intact.
Flapjack infrastructure; no preservation law is assumed in its premises. -/
theorem pushedHandlerStateOccupiedSuffix {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (a b register : Nat)
    (savedHandler : WordLocW width) (room : 3 ≤ source.stackSpace) :
    (pushedHandlerState source a b register savedHandler).stack.drop source.stackSpace =
      source.stack.drop source.stackSpace := by
  simp only [pushedHandlerState]
  rw [List.drop_set_of_lt (by omega), List.drop_set_of_lt (by omega),
    List.drop_set_of_lt (by omega)]

/-- The actual occupied-word observation is shifted by precisely three saved
handler slots. Derived from the real writes and total EL, with no default change. -/
theorem pushedHandlerStateOccupiedWords {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (a b register : Nat)
    (savedHandler : WordLocW width) (room : 3 ≤ source.stackSpace) (index : Nat) :
    holEl index (source.stack.drop source.stackSpace) =
      holEl (index + 3)
        ((pushedHandlerState source a b register savedHandler).stack.drop
          (pushedHandlerState source a b register savedHandler).stackSpace) := by
  have occupied := congrArg (holEl index)
    (pushedHandlerStateOccupiedSuffix source a b register savedHandler room)
  rw [holElDrop, holElDrop] at occupied
  rw [holElDrop, holElDrop]
  change holEl (source.stackSpace + index) source.stack =
    holEl (source.stackSpace - 3 + (index + 3))
      (pushedHandlerState source a b register savedHandler).stack
  rw [show source.stackSpace - 3 + (index + 3) = source.stackSpace + index by omega]
  exact occupied.symm

/-- Successful normal-frame decoding gains exactly the three saved handler
words when its source frame gains a handler. No decoder outcome is assumed
for the new frame; it is derived from the old native decoding. -/
theorem absStackAddHandler {width frameWidth : Nat} [NeZero width] [NeZero frameWidth]
    (bs : List (BitVec width)) (n : Option Nat) (l0 l : List (Nat × WordLocW frameWidth))
    (saved : Nat × Nat × Nat) (rest : List (WordSemStackFrame frameWidth))
    (words : List (WordLocW width)) (lens : List Nat) (frameLength : Nat)
    (bits : List Bool) (payload : List (WordLocW width))
    (tail : List (Option (WordLocW width × WordLocW width) × List Bool × List (WordLocW width)))
    (loc handler : WordLocW width)
    (decoded : absStack bs (.stackFrame n l0 l none :: rest) words (frameLength :: lens) =
      some ((none,bits,payload) :: tail)) :
    absStack bs (.stackFrame n l0 l (some saved) :: rest)
      (.word 1 :: loc :: handler :: words) (frameLength :: lens) =
        some ((some (loc,handler),bits,payload) :: tail) := by
  obtain ⟨bitmap, body, actualBits, actualTail, rfl, read, lengthEq, bound, recurse, equality⟩ :=
    CallReturnSupport.absStack_cons_none bs n l0 l rest words frameLength lens
      ((none,bits,payload) :: tail) decoded
  simp only [List.cons.injEq, Prod.mk.injEq] at equality
  obtain ⟨⟨_, rfl, rfl⟩, rfl⟩ := equality
  simp [absStack, read, lengthEq, Nat.not_lt.mpr bound, recurse]

/-- Full stack-relation transition when the current normal frame gains the
saved source handler and label. The new decoder and saved-handler obligation
are derived from the original relation; no postrelation is assumed. -/
theorem stackRelAddHandler {width : Nat} [NeZero width]
    (k oldHandler a b : Nat) (n : Option Nat) (l0 l : List (Nat × WordLocW width))
    (rest : List (WordSemStackFrame width)) (words : List (WordLocW width))
    (len : Nat) (bs : List (BitVec width)) (frameLength : Nat) (lens : List Nat)
    (savedHandler : WordLocW width)
    (relation : stackRel k oldHandler (.stackFrame n l0 l none :: rest)
      (some savedHandler) words len bs (frameLength :: lens)) :
    stackRel k rest.length (.stackFrame n l0 l (some (oldHandler,a,b)) :: rest)
      (some (.word (BitVec.ofNat width (len - (words.length + 3)))))
      (.word 1 :: .loc a b :: savedHandler :: words) len bs (frameLength :: lens) := by
  obtain ⟨sorted, astack, decoded, handler, auxiliary⟩ := relation
  obtain ⟨bitmap, body, bits, tail, wordsEq, read, bitLength, bodyBound, recurse, shape⟩ :=
    CallReturnSupport.absStack_cons_none bs n l0 l rest words frameLength lens astack decoded
  subst astack
  have lengths : tail.length = rest.length := (absStackImpLength _ _ _ _ _ recurse).1
  have newDecoded := absStackAddHandler bs n l0 l (oldHandler,a,b) rest words lens
    frameLength bits (body.take frameLength) tail (.loc a b) savedHandler decoded
  have newLength := absStackToStackLength bs _ _ _ _ newDecoded
  refine ⟨?_, _, newDecoded, ?_, ?_⟩
  · simpa only [List.all_cons, sortedEnv] using sorted
  · intro _ _
    simp only [List.length_cons]
    rw [show tail.length + 1 - (rest.length + 1) = 0 by omega, List.drop_zero, newLength]
    simp only [List.length_cons]
  · simp only [stackRelAux] at auxiliary ⊢
    refine ⟨?_, True.intro, auxiliary⟩
    intro bound active
    have sourceBound : oldHandler < (.stackFrame n l0 l none :: rest).length := by
      simp only [List.length_cons]; omega
    have saved := handler sourceBound (by
      simp only [List.length_cons]
      rw [show rest.length + 1 - (oldHandler + 1) =
        (rest.length - (oldHandler + 1)) + 1 by omega, holEl_cons_succ]
      simpa only [lengths] using active)
    apply Option.some.inj at saved
    simp only [List.length_cons] at saved
    rw [show tail.length + 1 - (oldHandler + 1) =
      (tail.length - (oldHandler + 1)) + 1 by omega, List.drop_succ_cons] at saved
    exact saved

/-- Derive the original stack-size relation after adding the three handler
slots. Source optional maxima and frame-size predictions are unrestricted;
only actual source space bounds are used. No new resource relation is assumed. -/
theorem stackSizeRelAddHandler {width : Nat} [NeZero width] {α : Type}
    (n : Option Nat) (l0 l : List (Nat × WordLocW width)) (saved : Nat × Nat × Nat)
    (rest : List (WordSemStackFrame width)) (limit : Nat) (maximum : Option Nat)
    (words : List α) (space : Nat) (room : 3 ≤ space) (bound : space ≤ words.length)
    (relation : stackSizeRel 0 (some 0) limit
      (wordSemOptionMax maximum (wordSemStackSize (.stackFrame n l0 l none :: rest)))
      (.stackFrame n l0 l none :: rest) words space 0) :
    stackSizeRel 0 (some 0) limit
      (wordSemOptionMax maximum (wordSemStackSize (.stackFrame n l0 l (some saved) :: rest)))
      (.stackFrame n l0 l (some saved) :: rest) words (space - 3) 0 := by
  have oldSize : wordSemStackSize (.stackFrame n l0 l none :: rest) =
      wordSemOptionAdd n (wordSemStackSize rest) := rfl
  have newSize : wordSemStackSize (.stackFrame n l0 l (some saved) :: rest) =
      wordSemOptionAdd (n.map (fun size => 3 + size)) (wordSemStackSize rest) := rfl
  simp only [stackSizeRel, oldSize, newSize] at relation ⊢
  cases n <;> cases maximum <;> cases tailSize : wordSemStackSize rest <;>
    simp_all [wordSemOptionAdd, wordSemOptionMax]
  all_goals
    obtain ⟨limitEq, maximumBound, sizeEq⟩ := relation
    constructor <;> omega

/-- Actual allocated suffix is the original handler header followed by the
unchanged occupied stack. Its three available cells are derived from bounds. -/
theorem pushedHandlerStateHeader {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (a b register : Nat)
    (savedHandler : WordLocW width) (room : 3 ≤ source.stackSpace)
    (bound : source.stackSpace ≤ source.stack.length) :
    (pushedHandlerState source a b register savedHandler).stack.drop
      (pushedHandlerState source a b register savedHandler).stackSpace =
      .word 1 :: .loc a b :: savedHandler :: source.stack.drop source.stackSpace := by
  have available : 3 ≤ (source.stack.drop (source.stackSpace - 3)).length := by
    simp only [List.length_drop]
    omega
  rcases headerShape : source.stack.drop (source.stackSpace - 3) with
    _ | ⟨x, _ | ⟨y, _ | ⟨z, tail⟩⟩⟩ <;>
    simp only [headerShape, List.length_nil, List.length_cons] at available
  all_goals try omega
  have tailEq : tail = source.stack.drop source.stackSpace := by
    have shifted := congrArg (List.drop 3) headerShape
    simp only [List.drop_drop, List.drop_succ_cons, List.drop_zero] at shifted
    rw [show source.stackSpace - 3 + 3 = source.stackSpace by omega] at shifted
    exact shifted.symm
  simp only [pushedHandlerState]
  rw [List.drop_set, if_neg (by omega), List.drop_set, if_neg (by omega),
    List.drop_set, if_neg (by omega), headerShape]
  simp only [Nat.add_sub_cancel_left, Nat.sub_self, List.set_cons_zero,
    List.set_cons_succ, tailEq]

/-- Assemble the full original final state relation from actual header updates.
Saved handler lookup is an intermediate source observation, not a target run
or desired postrelation assumption. This is transition infrastructure. -/
theorem stateRelPushedHandler {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (register f' a b retValue : Nat)
    (retProgram : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (envs : Spt (WordLocW width) × Spt (WordLocW width)) (lens : List Nat)
    (savedHandler : WordLocW width) (saved : target.store.lookup .handler = some savedHandler)
    (room : 3 ≤ target.stackSpace)
    (relation : stateRel ac register 0 0
      {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
      target (f' :: lens) 0) :
    stateRel ac register 0 0
      {WordSemStateFiniteExact.pushEnv envs (some (retValue,retProgram,a,b)) source
        with locals := .ln, localsSize := some 0}
      (pushedHandlerState target a b register savedHandler) (f' :: lens) 0 := by
  have erased : ((target.store.updateEq (.handler,
      .word (BitVec.ofNat width (target.stackSpace - 3)))).eraseEq .handler) =
      target.store.eraseEq .handler := by
    apply HolFiniteMapExact.ext_lookup
    intro key
    simp only [HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL]
    by_cases equal : key = .handler
    · simp [equal]
    · simp [equal, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  unfold stateRel at relation ⊢
  dsimp only [WordSemStateFiniteExact.pushEnv, pushedHandlerState] at relation ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38⟩ := relation
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_, h13, h14, h15, h16, ?_, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, ?_, ?_, h35, h36, ?_, ?_⟩
  · rw [erased]
    exact h12
  · simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  · simp only [List.length_set]
    simp only [Nat.add_zero] at h33 ⊢
    omega
  · simpa only [List.length_set] using h34
  · have sizes := stackSizeRelAddHandler source.localsSize (sptToAList envs.1)
      (wordSemEnvToList envs.2 source.permute).1 (source.handler,a,b) source.stack
      source.stackLimit source.stackMax target.stack target.stackSpace room
      (by simpa only [Nat.add_zero] using h33) h37
    simpa only [stackSizeRel, List.length_set] using sizes
  · simp only [Nat.add_zero, List.drop_zero, List.take_zero, sptLookup_ln,
      reduceCtorEq, false_implies, forall_const, and_true] at h38 ⊢
    rw [saved] at h38
    have related := stackRelAddHandler register source.handler a b source.localsSize
      (sptToAList envs.1) (wordSemEnvToList envs.2 source.permute).1 source.stack
      (target.stack.drop target.stackSpace) target.stack.length target.bitmaps f' lens
      savedHandler h38
    have pointer : target.stack.length -
        ((target.stack.drop target.stackSpace).length + 3) = target.stackSpace - 3 := by
      simp only [List.length_drop]
      simp only [Nat.add_zero] at h33
      omega
    have header := pushedHandlerStateHeader target a b register savedHandler room
      (by simpa only [Nat.add_zero] using h33)
    dsimp only [pushedHandlerState] at header
    rw [header]
    simpa only [List.length_set, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
      ite_true, pointer] using related

/-- Source-state codec for the actual imported canonical carrier.
Representation infrastructure, no separate HOL declaration. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Target-state codec for the actual imported canonical carrier.
Representation infrastructure, no separate HOL declaration. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original evaluate_PushHandler: its three original input guards imply
the actual successful native run and all unchanged-field, occupied-word,
unrelated-register, stack-space, length and final state-relation conjuncts.
The final relation is proved for the actual pushed source handler frame; it is
not a premise. Total HOL EL is retained, with no chosen past-end default.
Canonical maps and positive word/FFI dimensions use only the named translations.
The state/evaluator closure inherits reals_as_rational_cuts (SOUNDNESS item 8);
this is handler simulation, not whole compiler or numeric FP correspondence. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_PushHandler"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluatePushHandler {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (register f f' a b retValue : Nat)
    (retProgram : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (envs : Spt (WordLocW width) × Spt (WordLocW width)) (lens : List Nat)
    (room : 3 ≤ target.stackSpace)
    (relation : stateRel ac register 0 0
      {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
      target (f' :: lens) 0)
    (location : StackSem.locCheckExact target.code (a,b)) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (pushHandlerNative false a b (register,f,f'), target) =
        (none,post) ∧
      post = {target with
        stackSpace := post.stackSpace, regs := post.regs,
        stack := post.stack, store := post.store} ∧
      (∀ index, index < target.stack.length - target.stackSpace →
        holEl index (target.stack.drop target.stackSpace) =
          holEl (index + 3) (post.stack.drop post.stackSpace)) ∧
      (∀ index, index ≠ register → StackSemStateOps.getVar index post =
        StackSemStateOps.getVar index target) ∧
      post.stackSpace + 3 = target.stackSpace ∧
      post.stack.length = target.stack.length ∧
      stateRel ac register 0 0
        {WordSemStateFiniteExact.pushEnv envs (some (retValue,retProgram,a,b)) source
          with locals := .ln, localsSize := some 0}
        post (f' :: lens) 0 := by
  obtain ⟨savedHandler, saved, execution⟩ := evaluatePushHandlerFromStateRel ac register f f'
    a b source target envs lens room relation location
  have resources := pushedHandlerStateResources target a b register savedHandler room
  refine ⟨pushedHandlerState target a b register savedHandler, execution, ?_, ?_,
    resources.1, resources.2.1, resources.2.2, ?_⟩
  · rfl
  · intro index _
    exact pushedHandlerStateOccupiedWords target a b register savedHandler room index
  · exact stateRelPushedHandler ac register f' a b retValue retProgram source target envs lens
      savedHandler saved room relation

end Flapjack.WordToStackProofs.CallReturnHandler
