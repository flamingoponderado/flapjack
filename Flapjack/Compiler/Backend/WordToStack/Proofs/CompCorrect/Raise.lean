import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Seq
import Flapjack.Compiler.Backend.WordToStack.Proofs.HandlerTransition
import Flapjack.Compiler.Backend.WordToStack.Proofs.StackRelAuxStackSize
import Flapjack.Compiler.Backend.WordToStack.Proofs.Stubs
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StateLaws
import Flapjack.FiniteMap.MapKeys

namespace Flapjack.WordToStackProofs.CompCorrect.Raise
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-- Inhabitation only for original total EL; no unspecified value is selected. -/
local instance {width : Nat} [NeZero width] : Nonempty (WordLocW width) := ⟨.word 0⟩
local instance {width : Nat} [NeZero width] : Nonempty (WordSemStackFrame width) :=
  ⟨.stackFrame none [] [] none⟩

/-- Flapjack-only elimination of the original Raise source execution premise.
No source success, handler validity or poststate is supplied separately.
This is an internal step of the full constructor, not a separate HOL port. -/
theorem sourceRaiseSuccess {width : Nat} [NeZero width] {C F : Type}
    (name : Nat) (source sourcePost : WordSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (execution : WordSemStateFiniteExact.evaluate (.raise name) source = (result, sourcePost))
    (notError : result ≠ some .error) :
    ∃ value l1 l2,
      WordSemStateFiniteExact.getVar name source = some value ∧
      WordSemStateFiniteExact.jumpExc source = some (sourcePost, l1, l2) ∧
      result = some (.exception (.loc l1 l2) value) := by
  rw [WordSemStateFiniteExact.evaluate] at execution
  cases valueEq : WordSemStateFiniteExact.getVar name source with
  | none => simp [valueEq] at execution; exact False.elim (notError execution.1.symm)
  | some value =>
    rw [valueEq] at execution
    cases jumpEq : WordSemStateFiniteExact.jumpExc source with
    | none => simp [jumpEq] at execution; exact False.elim (notError execution.1.symm)
    | some next =>
      rcases next with ⟨next, l1, l2⟩
      rw [jumpEq] at execution
      obtain ⟨resultEq, postEq⟩ := Prod.mk.inj execution
      subst next
      exact ⟨value, l1, l2, rfl, rfl, resultEq.symm⟩

/-- Flapjack-only exposure of the actual source handler frame from a
successful jump. The full case supplies this premise by sourceRaiseSuccess;
no target header, postrelation or extra handler validity is assumed. -/
theorem sourceHandlerFrame {width : Nat} [NeZero width] {C F : Type}
    (source sourcePost : WordSemStateFiniteExact width C F) (l1 l2 : Nat)
    (jump : WordSemStateFiniteExact.jumpExc source = some (sourcePost, l1, l2)) :
    ∃ size nonGc gc oldHandler rest,
      source.handler < source.stack.length ∧
      wordSemLastN (source.handler + 1) source.stack =
        .stackFrame size nonGc gc (some (oldHandler,l1,l2)) :: rest ∧
      sourcePost = { source with
        handler := oldHandler
        locals := sptUnion (sptFromAList gc) (sptFromAList nonGc)
        stack := rest
        localsSize := size } := by
  unfold WordSemStateFiniteExact.jumpExc at jump
  split at jump
  · rename_i bound
    cases suffixEq : wordSemLastN (source.handler + 1) source.stack with
    | nil => simp [suffixEq] at jump
    | cons frame rest =>
      cases frame with
      | stackFrame size nonGc gc handler =>
        cases handler with
        | none => simp [suffixEq] at jump
        | some h =>
          rcases h with ⟨oldHandler, x, y⟩
          simp only [suffixEq, Option.some.injEq, Prod.mk.injEq] at jump
          rcases jump with ⟨postEq, xEq, yEq⟩
          subst x
          subst y
          exact ⟨size, nonGc, gc, oldHandler, rest, bound, rfl, postEq.symm⟩
  · simp at jump

/-- Flapjack-only total EL observation from an actual nonempty suffix.
The suffix equation supplies the nonempty case; no arbitrary value is chosen. -/
theorem lastNHeadEl {α : Type} [Nonempty α] (xs : List α) (n : Nat)
    (head : α) (tail : List α) (suffix : wordSemLastN n xs = head :: tail) :
    holEl (xs.length - n) xs = head := by
  rw [lastNDrop2] at suffix
  calc
    holEl (xs.length - n) xs = holEl 0 (xs.drop (xs.length - n)) := by
      simpa only [Nat.add_zero] using (holElDrop xs (xs.length - n) 0).symm
    _ = head := by rw [suffix]; rfl

/-- Flapjack-only extraction of the actual handler environment sorting.
It is inherited from the original full stack relation, not supplied anew. -/
theorem handlerEnvironmentSorted {width : Nat} [NeZero width]
    (frames : List (WordSemStackFrame width)) (handler : Nat)
    (size : Option Nat) (nonGc gc : List (Nat × WordLocW width))
    (h1 l1 l2 : Nat) (rest : List (WordSemStackFrame width))
    (sorted : frames.all sortedEnv = true)
    (suffix : wordSemLastN (handler + 1) frames =
      .stackFrame size nonGc gc (some (h1,l1,l2)) :: rest) :
    holSorted (fun x y => x.1 > y.1) gc := by
  have member : WordSemStackFrame.stackFrame size nonGc gc (some (h1,l1,l2)) ∈ frames := by
    have member : WordSemStackFrame.stackFrame size nonGc gc (some (h1,l1,l2)) ∈
        wordSemLastN (handler + 1) frames := by rw [suffix]; simp
    rw [lastNDrop2] at member
    exact List.mem_of_mem_drop member
  have ordered := List.all_eq_true.mp sorted _ member
  exact (descendingKeysIffHolSorted gc).mp ordered

/-- Flapjack-only discharge of the concrete unwind header obligations from
full stackRel and the actual source frame. The full case obtains rawWidth and
rawBound from stateRel; this helper is not a narrowed comp_correct port. -/
theorem relatedRaiseHeader {width : Nat} [NeZero width]
    (k handler n : Nat) (source : List (WordSemStackFrame width))
    (raw : List (WordLocW width)) (bitmaps : List (BitVec width)) (lens : List Nat)
    (targetHandler : Option (WordLocW width))
    (size : Option Nat) (nonGc gc : List (Nat × WordLocW width))
    (h1 l1 l2 : Nat) (rest : List (WordSemStackFrame width))
    (related : stackRel k handler source targetHandler (raw.drop n) raw.length bitmaps lens)
    (sourceBound : handler < source.length) (rawBound : n ≤ raw.length)
    (rawWidth : raw.length < 2 ^ width)
    (suffix : wordSemLastN (handler + 1) source =
      .stackFrame size nonGc gc (some (h1,l1,l2)) :: rest) :
    ∃ offset saved,
      targetHandler = some (.word (BitVec.ofNat width offset)) ∧
      offset < 2 ^ width ∧ offset + 3 ≤ raw.length ∧
      raw[offset + 1]? = some (.loc l1 l2) ∧ raw[offset + 2]? = some saved := by
  rcases related with ⟨sorted, stack, decoded, handlerEq, aux⟩
  have sortedGc := handlerEnvironmentSorted source handler size nonGc gc h1 l1 l2 rest sorted suffix
  have active : isHandlerFrame (holEl (source.length - (handler + 1)) source) = true := by
    rw [lastNHeadEl source (handler + 1) _ rest suffix]
    rfl
  have targetHandlerEq := handlerEq sourceBound active
  obtain ⟨ex, payload, shape, _rawMin, suffixMin, location, _saved,
      _cleared, _clearedDecoded⟩ := stackRelRaise bitmaps source raw lens stack n handler k
        size nonGc gc h1 l1 l2 rest rawBound (by omega) sortedGc suffix decoded aux
  have suffixBound := absStackLen bitmaps source (raw.drop n) lens stack (handler + 1) decoded
  simp only [List.length_drop] at suffixBound
  let offset := raw.length - handlerVal (wordSemLastN (handler + 1) stack)
  have space : offset + 3 ≤ raw.length := by dsimp [offset]; omega
  have locationBound : offset + 1 < raw.length := by omega
  have savedBound : offset + 2 < raw.length := by omega
  refine ⟨offset, raw[offset + 2], ?_, ?_, space, ?_, ?_⟩
  · simpa only [lastNDrop2, offset] using targetHandlerEq
  · dsimp [offset]; omega
  · rw [holEl_eq_getElem _ raw locationBound] at location
    simpa only [List.getElem?_eq_getElem locationBound] using congrArg some location
  · simp only [List.getElem?_eq_getElem savedBound]

/-- Flapjack-only full cleared stackRel stage of Raise. The original
handler transition supplies both cleared decoder and auxiliary relation;
the saved-handler conditional is transported through the cleared frame,
including the boundary case where that frame itself is not a handler. -/
theorem clearedHandlerStackRel {width : Nat} [NeZero width]
    (k handler n : Nat) (source : List (WordSemStackFrame width))
    (raw : List (WordLocW width)) (bitmaps : List (BitVec width)) (lens : List Nat)
    (stack : List (Option (WordLocW width × WordLocW width) × List Bool × List (WordLocW width)))
    (size : Option Nat) (nonGc gc : List (Nat × WordLocW width))
    (h1 l1 l2 : Nat) (rest : List (WordSemStackFrame width))
    (rawBound : n ≤ raw.length) (bound : handler + 1 ≤ source.length)
    (sorted : source.all sortedEnv = true)
    (suffix : wordSemLastN (handler + 1) source =
      .stackFrame size nonGc gc (some (h1,l1,l2)) :: rest)
    (decoded : absStack bitmaps source (raw.drop n) lens = some stack)
    (aux : stackRelAux k raw.length source stack) :
    let offset := raw.length - handlerVal (wordSemLastN (handler + 1) stack)
    stackRel k h1 (.stackFrame size nonGc gc none :: rest)
      (some (holEl (offset + 2) raw)) (raw.drop (offset + 3)) raw.length bitmaps
      (wordSemLastN (handler + 1) lens) := by
  have sortedGc := handlerEnvironmentSorted source handler size nonGc gc h1 l1 l2 rest sorted suffix
  have envEq := sortedEnvironmentIdentity gc ((descendingKeysIffHolSorted gc).mpr sortedGc)
  obtain ⟨ex,payload,shape,_rawMin,_suffixMin,_location,saved,cleared,clearedDecoded⟩ :=
    stackRelRaise bitmaps source raw lens stack n handler k size nonGc gc h1 l1 l2 rest
      rawBound bound sortedGc suffix decoded aux
  rw [envEq] at cleared clearedDecoded
  have tailLength := (absStackImpLength bitmaps
    (.stackFrame size nonGc gc none :: rest) _ _ _ clearedDecoded).1
  simp only [List.length_cons] at tailLength
  have sortedSuffix : (.stackFrame size nonGc gc (some (h1,l1,l2)) :: rest).all sortedEnv = true := by
    apply List.all_eq_true.mpr
    intro frame member
    apply List.all_eq_true.mp sorted frame
    have suffixMember : frame ∈ wordSemLastN (handler + 1) source := by rw [suffix]; exact member
    rw [lastNDrop2] at suffixMember
    exact List.mem_of_mem_drop suffixMember
  refine ⟨?_, (none,payload) :: wordSemLastN handler stack, clearedDecoded, ?_, cleared⟩
  · simpa only [List.all_cons, sortedEnv] using sortedSuffix
  · intro activeBound active
    by_cases edge : h1 = rest.length
    · subst h1
      simp [holEl, holHd, isHandlerFrame] at active
    · have oldBound : h1 < rest.length := by simp only [List.length_cons] at activeBound; omega
      have indexEq : (rest.length + 1) - (h1 + 1) = (rest.length - (h1 + 1)) + 1 := by omega
      have oldActive : isHandlerFrame (holEl (rest.length - (h1 + 1)) rest) = true := by
        simpa only [List.length_cons, indexEq, holEl_cons_succ] using active
      have savedEq := saved ⟨oldBound,oldActive⟩
      rw [shape] at savedEq
      have within : h1 + 1 ≤ (wordSemLastN handler stack).length := by omega
      rw [lastNConsWithin (some ex,payload) (wordSemLastN handler stack) (h1 + 1) within] at savedEq
      change some (holEl (raw.length - handlerVal (wordSemLastN (handler + 1) stack) + 2) raw) = _
      rw [shape, savedEq, ← lastNDrop2,
        lastNConsWithin (none,payload) (wordSemLastN handler stack) (h1 + 1) within]

/-- Flapjack-only concrete final target state of the actual non-instrumented
unwind stub. All intermediate register writes are recorded literally. -/
noncomputable def unwindTarget {width : Nat} [NeZero width] {C F : Type}
    (target : StackSemStateFiniteExact width C F) (k offset l1 l2 : Nat)
    (saved : WordLocW width) : StackSemStateFiniteExact width C F :=
  { target with
    regs := (((target.regs.updateEq (k, .word (BitVec.ofNat width offset))).updateEq
      (k, .word (BitVec.ofNat width offset <<< wordShiftAmount width))).updateEq
      (k, saved)).updateEq (k, .loc l1 l2)
    store := target.store.updateEq (.handler, saved)
    stackSpace := offset + 3 }

/-- Flapjack-only execution of the actual eight-command unwind stub from its
concrete header fields. The full case must derive these fields and bounds from
stateRel and stackRelRaise; this helper is not tagged as comp_correct and does
not take the target run or a postrelation as a premise. -/
theorem evaluateUnwindTarget {width : Nat} [NeZero width] {C F : Type}
    (target : StackSemStateFiniteExact width C F) (k offset l1 l2 : Nat)
    (saved : WordLocW width)
    (useStack : target.useStack = true) (useStore : target.useStore = true)
    (handler : target.store.lookup .handler = some (.word (BitVec.ofNat width offset)))
    (offsetWidth : offset < 2 ^ width) (space : offset + 3 ≤ target.stack.length)
    (location : target.stack[offset + 1]? = some (.loc l1 l2))
    (savedWord : target.stack[offset + 2]? = some saved) :
    StackSemEvaluate.evaluate (@raiseStubNative width _ false k, target) =
      (some (.exception (.loc l1 l2)), unwindTarget target k offset l1 l2 saved) := by
  have offsetBound : offset < target.stack.length := by omega
  have locationBound : offset + 1 < target.stack.length := by omega
  have savedBound : offset + 2 < target.stack.length := by omega
  have locationValue : target.stack[offset + 1] = .loc l1 l2 := by
    simpa only [List.getElem?_eq_getElem locationBound, Option.some.injEq] using location
  have savedValue : target.stack[offset + 2] = saved := by
    simpa only [List.getElem?_eq_getElem savedBound, Option.some.injEq] using savedWord
  have wordNat : (BitVec.ofNat width offset).toNat = offset := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt offsetWidth]
  simp [raiseStubFalse, StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_get,
    StackSemEvaluate.evaluate_stackSetSize, StackSemEvaluate.evaluate_skip,
    StackSemEvaluate.evaluate_stackLoad, StackSemEvaluate.evaluate_set,
    StackSemEvaluate.evaluate_stackFree, StackSemEvaluate.evaluate_raise,
    StackSemStateOps.setVar, StackSemStateOps.getVar, StackSemStateOps.setStore,
    StackSemControl.fixClock, StackSemRegisterTransfers.storeOfSyntax,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    useStack, useStore, handler, wordNat, locationBound, savedBound,
    locationValue, savedValue, Nat.not_le_of_gt offsetBound,
    Nat.not_lt_of_ge space, unwindTarget]

/-- Flapjack-only execution of the actual compiled Raise call, with the
original one-extra-clock witness. Header premises are discharged by the full
case from the original relation; no target evaluation is assumed. -/
theorem evaluateRaiseCall {width : Nat} [NeZero width] {C F : Type}
    (target : StackSemStateFiniteExact width C F) (k offset l1 l2 : Nat)
    (saved : WordLocW width)
    (stub : sptLookup raiseStubLocation target.code = some (@raiseStubNative width _ false k))
    (useStack : target.useStack = true) (useStore : target.useStore = true)
    (handler : target.store.lookup .handler = some (.word (BitVec.ofNat width offset)))
    (offsetWidth : offset < 2 ^ width) (space : offset + 3 ≤ target.stack.length)
    (location : target.stack[offset + 1]? = some (.loc l1 l2))
    (savedWord : target.stack[offset + 2]? = some saved) :
    StackSemEvaluate.evaluate
      ((.call none (.inl raiseStubLocation) none : HolProg width),
        {target with clock := target.clock + 1}) =
      (some (.exception (.loc l1 l2)), unwindTarget target k offset l1 l2 saved) := by
  have run := evaluateUnwindTarget target k offset l1 l2 saved useStack useStore
    handler offsetWidth space location savedWord
  simp [StackSemEvaluate.evaluate_call, StackSemControl.findCode, stub,
    StackSemStateOps.decClock, run, StackSemControl.fixClock,
    StackSemControl.badFunReturn, unwindTarget]

/-- Flapjack-only resource stage of the original Raise case. The complete
stackSizeRel after clearing the handler frame follows from its original
resource relation, suffix equation and auxiliary relation. Neither a source
successful stack-size computation nor a target resource postcondition is
assumed separately. -/
theorem raiseStackSizeRelation {width : Nat} [NeZero width]
    (k handler frame sourceSpace : Nat) (localsSize : Option Nat)
    (stackLimit : Nat) (stackMax : Option Nat)
    (source : List (WordSemStackFrame width)) (raw : List (WordLocW width))
    (size : Option Nat) (nonGc gc : List (Nat × WordLocW width))
    (h1 l1 l2 : Nat) (rest : List (WordSemStackFrame width))
    (ex : WordLocW width × WordLocW width) (bits : List Bool)
    (payload : List (WordLocW width))
    (tail : List (Option (WordLocW width × WordLocW width) × List Bool × List (WordLocW width)))
    (resource : stackSizeRel frame localsSize stackLimit stackMax source raw sourceSpace 0)
    (bound : handler + 1 ≤ source.length)
    (suffix : wordSemLastN (handler + 1) source =
      .stackFrame size nonGc gc (some (h1,l1,l2)) :: rest)
    (aux : stackRelAux k raw.length
      (.stackFrame size nonGc gc (some (h1,l1,l2)) :: rest)
      ((some ex,bits,payload) :: tail))
    (rawBound : handlerVal ((some ex,bits,payload) :: tail) ≤ raw.length) :
    stackSizeRel 0 (some 0) stackLimit stackMax
      (.stackFrame size nonGc gc none :: rest) raw
      (raw.length - handlerVal ((some ex,bits,payload) :: tail) + 3) 0 := by
  rcases resource with ⟨_localsFrame, limit, maxima⟩
  refine ⟨by simp, limit, ?_⟩
  intro maximum maximumEq
  obtain ⟨maximumBound, _localsSome, x, sourceSize, xEq⟩ := maxima maximum maximumEq
  obtain ⟨y, suffixSize, yBound⟩ := lastNStackSizeSome (handler + 1) source _ x
    ⟨suffix, sourceSize, bound⟩
  have yEq := stackRelAuxStackSize k raw.length _ _ aux
  rw [suffixSize] at yEq
  simp only [miscThe] at yEq
  change wordSemOptionAdd (size.map (fun n => 3 + n)) (wordSemStackSize rest) = some y at suffixSize
  cases size with
  | none => simp [wordSemOptionAdd] at suffixSize
  | some localSize =>
    cases restSize : wordSemStackSize rest with
    | none => simp [restSize, wordSemOptionAdd] at suffixSize
    | some restSizeValue =>
      simp only [Option.map_some, restSize, wordSemOptionAdd, Option.some.injEq] at suffixSize
      have clearedSize : wordSemStackSize (.stackFrame (some localSize) nonGc gc none :: rest) =
          some (localSize + restSizeValue) := by
        change wordSemOptionAdd (some localSize) (wordSemStackSize rest) = _
        rw [restSize]
        rfl
      have arithmetic : raw.length -
          (raw.length - handlerVal ((some ex,bits,payload) :: tail) + 3) - 0 - 0 =
          localSize + restSizeValue := by
        simp only [handlerVal] at yEq rawBound ⊢
        omega
      refine ⟨?_, by simp, localSize + restSizeValue, clearedSize, arithmetic.symm⟩
      rw [arithmetic]
      omega

/-- Flapjack-only canonical store equation: updating the handler field does
not change the same map with that field erased. -/
theorem eraseUpdatedHandler {width : Nat} [NeZero width]
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (saved : WordLocW width) :
    (store.updateEq (.handler,saved)).eraseEq .handler = store.eraseEq .handler := by
  apply HolFiniteMapExact.ext_lookup
  intro key
  by_cases same : key = .handler
  · subst key
    simp [HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL]
  · simp [HolFiniteMapExact.lookup_eraseEq, HolFiniteMapExact.lookup_updateEq,
      FUPDATE_HOL, FDOMSUB_HOL, same]

/-- Flapjack-only source state after jumping to the handler and pushing its
cleared frame, definitionally the original pushLocals of the jump result. -/
def clearedSource {width : Nat} [NeZero width] {C F : Type}
    (source : WordSemStateFiniteExact width C F) (size : Option Nat)
    (nonGc gc : List (Nat × WordLocW width)) (h1 : Nat)
    (rest : List (WordSemStackFrame width)) : WordSemStateFiniteExact width C F :=
  { source with
    locals := .ln
    localsSize := some 0
    handler := h1
    stack := .stackFrame size nonGc gc none :: rest }

/-- Flapjack-only composition of the entire cleared stateRel used in Raise.
The source suffix, original full relation and actual decoder determine the
poststate; no target run or postrelation is supplied as a premise. -/
theorem fullRaisePostRelation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (size : Option Nat) (nonGc gc : List (Nat × WordLocW width))
    (h1 l1 l2 : Nat) (rest : List (WordSemStackFrame width))
    (related : stateRel ac k f frame source target lens 0)
    (sourceBound : source.handler < source.stack.length)
    (suffix : wordSemLastN (source.handler + 1) source.stack =
      .stackFrame size nonGc gc (some (h1,l1,l2)) :: rest) :
    ∃ offset saved,
      stateRel ac k 0 0 (clearedSource source size nonGc gc h1 rest)
        (unwindTarget target k offset l1 l2 saved)
        (wordSemLastN (source.handler + 1) lens) 0 ∧
      target.store.lookup .handler = some (.word (BitVec.ofNat width offset)) ∧
      offset < 2 ^ width ∧ offset + 3 ≤ target.stack.length ∧
      target.stack[offset + 1]? = some (.loc l1 l2) ∧ target.stack[offset + 2]? = some saved := by
  have fields : target.stackSpace + f ≤ target.stack.length ∧
      target.stack.length < 2 ^ width ∧
      stackSizeRel f source.localsSize source.stackLimit source.stackMax source.stack
        target.stack target.stackSpace 0 ∧
      stackRel k source.handler source.stack (target.store.lookup .handler)
        (target.stack.drop (target.stackSpace + f)) target.stack.length target.bitmaps lens := by
    simp only [stateRel, Nat.add_zero, List.drop_drop] at related
    tauto
  rcases fields.2.2.2 with ⟨sorted,stack,decoded,handlerEq,aux⟩
  have sortedGc := handlerEnvironmentSorted source.stack source.handler size nonGc gc h1 l1 l2
    rest sorted suffix
  have active : isHandlerFrame (holEl (source.stack.length - (source.handler + 1)) source.stack) = true := by
    rw [lastNHeadEl source.stack (source.handler + 1) _ rest suffix]
    rfl
  have handler := handlerEq sourceBound active
  obtain ⟨ex,bits,payload,shape,_suffixDecoded,suffixAux⟩ := handlerSuffixExtract target.bitmaps
    source.stack target.stack lens stack (target.stackSpace + f) source.handler k size nonGc gc
    (h1,l1,l2) rest (by omega) suffix decoded aux
  let offset := target.stack.length - handlerVal (wordSemLastN (source.handler + 1) stack)
  let saved := holEl (offset + 2) target.stack
  obtain ⟨_ex,_payload,_shape,_rawMin,minSize,location,_savedConditional,_cleared,_clearedDecoded⟩ :=
    stackRelRaise target.bitmaps source.stack target.stack lens stack (target.stackSpace + f)
      source.handler k size nonGc gc h1 l1 l2 rest fields.1 (by omega) sortedGc suffix decoded aux
  have suffixBound := absStackLen target.bitmaps source.stack
    (target.stack.drop (target.stackSpace + f)) lens stack (source.handler + 1) decoded
  simp only [List.length_drop] at suffixBound
  have space : offset + 3 ≤ target.stack.length := by dsimp [offset]; omega
  have locationBound : offset + 1 < target.stack.length := by omega
  have savedBound : offset + 2 < target.stack.length := by omega
  have resourcePost := raiseStackSizeRelation k source.handler f target.stackSpace source.localsSize
    source.stackLimit source.stackMax source.stack target.stack size nonGc gc h1 l1 l2 rest ex bits
    payload (wordSemLastN source.handler stack) fields.2.2.1 (by omega) suffix suffixAux
    (by rw [← shape]; omega)
  have stackPost := clearedHandlerStackRel k source.handler (target.stackSpace + f) source.stack
    target.stack target.bitmaps lens stack size nonGc gc h1 l1 l2 rest fields.1 (by omega)
    sorted suffix decoded aux
  have postResource : stackSizeRel 0 (some 0) source.stackLimit source.stackMax
      (.stackFrame size nonGc gc none :: rest) target.stack (offset + 3) 0 := by
    simpa only [offset, shape] using resourcePost
  refine ⟨offset,saved,?_,?_,?_,space,?_,?_⟩
  · simp only [stateRel, Nat.add_zero, List.drop_drop] at related
    rcases related with ⟨original1,original2,original3,original4,original5,original6,original7,original8,original9,original10,original11,original12,original13,original14,original15,original16,original17,original18,original19,original20,original21,original22,original23,original24,original25,original26,original27,original28,original29,original30,original31,original32,original33,original34,original35,original36⟩
    simp_all [stateRel, clearedSource, unwindTarget, eraseUpdatedHandler,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, offset, saved]
    constructor
    · intro index
      have info := original23 index
      exact ⟨info.1,info.2.1,info.2.2.1,info.2.2.2.1⟩
    · intro label program count codeLookup
      have info := original25 label program count codeLookup
      exact ⟨info.1,info.2.1⟩
  · simpa only [lastNDrop2, offset] using handler
  · dsimp [offset]; omega
  · rw [holEl_eq_getElem _ target.stack locationBound] at location
    simpa only [List.getElem?_eq_getElem locationBound] using congrArg some location
  · simp only [saved, holEl_eq_getElem _ target.stack savedBound,
      List.getElem?_eq_getElem savedBound]

/-- Flapjack-only full-premise execution stage of the original Raise case.
The actual run, handler headers and exception value register are all derived
from the source execution, conventions and full stateRel. This stage has no
HOL tag: the complete postrelation/resource conclusion is still assembled
below, and cannot be replaced by this execution-only result. -/
theorem relatedRaiseExecution {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (name k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (result : Option (WordSemResult width))
    (execution : WordSemStateFiniteExact.evaluate (.raise name) source = (result, sourcePost))
    (notError : result ≠ some .error)
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k (.raise name : WordLangProgHOL (BitVec width)) = true) :
    ∃ value l1 l2 offset saved,
      result = some (.exception (.loc l1 l2) value) ∧
      WordSemStateFiniteExact.jumpExc source = some (sourcePost,l1,l2) ∧
      StackSemEvaluate.evaluate
        ((.call none (.inl raiseStubLocation) none : HolProg width),
          {target with clock := target.clock + 1}) =
        (some (.exception (.loc l1 l2)), unwindTarget target k offset l1 l2 saved) ∧
      (unwindTarget target k offset l1 l2 saved).regs.lookup 1 = some value := by
  have nameEq : name = 2 := by
    simp only [postAllocConventionsHOL, Bool.and_eq_true] at conventions
    simpa [callArgConventionHOL] using conventions.2.2
  subst name
  obtain ⟨value, l1, l2, valueEq, jump, resultEq⟩ :=
    sourceRaiseSuccess 2 source sourcePost result execution notError
  obtain ⟨size, nonGc, gc, oldHandler, rest, sourceBound, suffix, _postEq⟩ :=
    sourceHandlerFrame source sourcePost l1 l2 jump
  have parts : target.useStack = true ∧ target.useStore = true ∧ 4 < k ∧
      sptLookup raiseStubLocation target.code = some (@raiseStubNative width _ false k) ∧
      target.stackSpace + f ≤ target.stack.length ∧ target.stack.length < 2 ^ width ∧
      stackRel k source.handler source.stack (target.store.lookup .handler)
        (target.stack.drop (target.stackSpace + f)) target.stack.length target.bitmaps lens := by
    simp only [stateRel, Nat.add_zero, List.drop_drop] at related
    tauto
  obtain ⟨offset, saved, handler, offsetWidth, space, location, savedWord⟩ :=
    relatedRaiseHeader k source.handler (target.stackSpace + f) source.stack target.stack
      target.bitmaps lens (target.store.lookup .handler) size nonGc gc oldHandler l1 l2 rest
      parts.2.2.2.2.2.2 sourceBound parts.2.2.2.2.1 parts.2.2.2.2.2.1 suffix
  have placed : target.regs.lookup 1 = some value := by
    have placement : ∀ n v, sptLookup n source.locals = some v →
        n % 2 = 0 ∧ if n / 2 < k then target.regs.lookup (n / 2) = some v
        else ((target.stack.drop target.stackSpace).take f)[f - 1 - (n / 2 - k)]? =
          some v ∧ n / 2 < k + frame := by
      simp only [stateRel, Nat.add_zero] at related
      repeat' (rcases related with ⟨_, related⟩)
      exact related
    have observed := placement 2 value valueEq
    simpa [show 1 < k by omega] using observed.2
  refine ⟨value,l1,l2,offset,saved,resultEq,jump,?_,?_⟩
  · exact evaluateRaiseCall target k offset l1 l2 saved parts.2.2.2.1 parts.1 parts.2.1
      handler offsetWidth space location savedWord
  · have distinct : 1 ≠ k := by omega
    simpa [unwindTarget, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, distinct] using placed

/-- Genuine canonical source codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Genuine canonical target codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original Raise constructor of comp_correct, including the original
clock existential and complete exception/resource result relation. The actual
handler run and cleared state relation are derived from the original premises.
Evaluator closure inherits reals_as_rational_cuts; this structural case makes
no numerical FP correspondence claim. The original hypotheses and entire conclusion are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectRaise {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (name : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    Seq.Simulation ac (.raise name) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  have compiledEq := congrArg Prod.fst compilation
  simp only [compNative] at compiledEq
  subst compiled
  have nameEq : name = 2 := by
    simp only [postAllocConventionsHOL, Bool.and_eq_true] at conventions
    simpa [callArgConventionHOL] using conventions.2.2
  subst name
  obtain ⟨value,l1,l2,valueEq,jump,resultEq⟩ :=
    sourceRaiseSuccess 2 source sourcePost result execution notError
  obtain ⟨size,nonGc,gc,oldHandler,rest,sourceBound,suffix,postEq⟩ :=
    sourceHandlerFrame source sourcePost l1 l2 jump
  obtain ⟨offset,saved,postRelation,handler,offsetWidth,space,location,savedWord⟩ :=
    fullRaisePostRelation ac k f frame source target lens size nonGc gc oldHandler l1 l2 rest
      related sourceBound suffix
  have parts : target.useStack = true ∧ target.useStore = true ∧ 4 < k ∧
      sptLookup raiseStubLocation target.code = some (@raiseStubNative width _ false k) := by
    simp only [stateRel] at related
    tauto
  have placed : target.regs.lookup 1 = some value := by
    have placement : ∀ n v, sptLookup n source.locals = some v →
        n % 2 = 0 ∧ if n / 2 < k then target.regs.lookup (n / 2) = some v
        else ((target.stack.drop target.stackSpace).take f)[f - 1 - (n / 2 - k)]? =
          some v ∧ n / 2 < k + frame := by
      simp only [stateRel,Nat.add_zero] at related
      repeat' (rcases related with ⟨_,related⟩)
      exact related
    have observed := placement 2 value valueEq
    simpa [show 1 < k by omega] using observed.2
  refine ⟨1,unwindTarget target k offset l1 l2 saved,some (.exception (.loc l1 l2)),?_,?_⟩
  · exact evaluateRaiseCall target k offset l1 l2 saved parts.2.2.2 parts.1 parts.2.1
      handler offsetWidth space location savedWord
  · rw [resultEq]
    simp only [compCorrectResult,Option.map,compileResult,ne_eq,not_true_eq_false,if_false]
    refine ⟨nonGc,gc,?_,?_,?_⟩
    · simpa only [postEq,pushLocals,clearedSource,lastNDrop2] using postRelation
    · simp only [postEq]
    · have distinct : 1 ≠ k := by omega
      simpa [unwindTarget,HolFiniteMapExact.lookup_updateEq,FUPDATE_HOL,distinct] using placed

end Flapjack.WordToStackProofs.CompCorrect.Raise
