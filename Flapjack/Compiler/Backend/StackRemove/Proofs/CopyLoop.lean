import Flapjack.Compiler.Backend.StackRemove.Proofs.CopyEach
import Flapjack.Compiler.Backend.StackProps.EvaluateAddClock
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateClock

namespace Flapjack.Compiler.Backend.StackRemove.CopyLoopProof
open Flapjack StackSemEvaluate StackSemStateOps Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Local exact state after the original load/increment prefix. The prefix
changes only register one and the bitmap pointer, and consumes no clock. -/
def loadBitmapState {width : Nat} [NeZero width] {C F : Type}
    (bitmap index : Nat) (base pattern : BitVec width)
    (target : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  {target with regs := (target.regs.updateEq (1, .word pattern)).updateEq (bitmap, .word (base + bytesInWord width * BitVec.ofNat width (index + 1)))}

set_option linter.unusedSimpArgs false in
/-- Native execution of the original two-instruction bitmap prefix. These
local input reads are derived from the original heap below, not premises of
an eventual HOL correctness theorem. -/
theorem loadBitmapRun {width : Nat} [NeZero width] {C F : Type}
    (bitmap index : Nat) (base pattern : BitVec width)
    (target : StackSemStateFiniteExact width C F)
    (distinct : bitmap ≠ 1)
    (read : getVar bitmap target =
      some (.word (base + bytesInWord width * BitVec.ofNat width index)))
    (load : memLoad (base + bytesInWord width * BitVec.ofNat width index) target =
      some (.word pattern)) :
    evaluate (listSeqHOL [loadInst 1 bitmap, addBytesInWordInst bitmap], target) =
      (none, loadBitmapState bitmap index base pattern target) := by
  change target.regs.lookup bitmap = _ at read
  have addressEq : base + bytesInWord width * BitVec.ofNat width index + bytesInWord width =
      base + bytesInWord width * BitVec.ofNat width (index + 1) := by
    simp [BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]
  dsimp only [bytesInWord] at read load addressEq
  simp [listSeqHOL, loadInst, addBytesInWordInst, evaluate_seq, evaluate_inst,
    StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    StackSemExpressions.assign, StackSemExpressions.wordExp,
    getVar, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    StackSemControl.fixClock, wordOpHOL, wordOp, wordSemBytesInWord,
    bytesInWord, distinct, read, load, loadBitmapState, ← addressEq]

/-- The actual original separated heap and source index bound derive the
native prefix execution, without a target load/domain/execution assumption. -/
theorem loadBitmapFromHeap {width : Nat} [NeZero width] {C F : Type}
    (temporary bitmap index : Nat) (base : BitVec width)
    (bitmaps : List (BitVec width)) (domain : BitVec width → Prop)
    (memory : BitVec width → WordLocW width)
    (rest : ((BitVec width × WordLocW width) → Prop) → Prop)
    (target : StackSemStateFiniteExact width C F)
    (distinct : [1, 2, 3, temporary, bitmap].Nodup)
    (bound : index < bitmaps.length)
    (read : getVar bitmap target =
      some (.word (base + bytesInWord width * BitVec.ofNat width index)))
    (heap : SetSep.star
      (SetSep.star (Misc.wordList base (bitmaps.map WordLocW.word)) rest)
      (memoryHOL memory domain)
      (SetSep.fun2Set (target.memory, fun key => target.mdomain key = true))) :
    evaluate (listSeqHOL [loadInst 1 bitmap, addBytesInWordInst bitmap], target) =
      (none, loadBitmapState bitmap index base bitmaps[index] target) := by
  have separate : bitmap ≠ 1 := by
    simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
    omega
  exact loadBitmapRun bitmap index base bitmaps[index] target separate read
    (CopyEachProof.bitmapLoad base bitmaps index domain memory rest target bound heap)

/-- Prefix registers required by CopyEach, derived from the original
three reads and register distinctness. All other state fields are preserved. -/
theorem loadBitmapReads {width : Nat} [NeZero width] {C F : Type}
    (temporary bitmap index : Nat) (base pattern address offset : BitVec width)
    (target : StackSemStateFiniteExact width C F)
    (distinct : [1, 2, 3, temporary, bitmap].Nodup)
    (addressRead : getVar 2 target = some (.word address))
    (offsetRead : getVar 3 target = some (.word offset)) :
    let next := loadBitmapState bitmap index base pattern target
    getVar 1 next = some (.word pattern) ∧
    getVar 2 next = some (.word address) ∧
    getVar 3 next = some (.word offset) ∧
    getVar bitmap next = some (.word
      (base + bytesInWord width * BitVec.ofNat width (index + 1))) ∧
    next.clock = target.clock := by
  have bOne : bitmap ≠ 1 := by
    simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
    omega
  have bTwo : bitmap ≠ 2 := by
    simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
    omega
  have bThree : bitmap ≠ 3 := by
    simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
    omega
  change target.regs.lookup 2 = _ at addressRead
  change target.regs.lookup 3 = _ at offsetRead
  simp [loadBitmapState, getVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    Ne.symm bOne, Ne.symm bTwo, Ne.symm bThree,
    addressRead, offsetRead]

/-- The native signed comparison driving CopyLoop is exactly the bitmap
sign bit. This follows from the two reviewed word operations directly. -/
theorem signedLessZero {width : Nat} [NeZero width] (pattern : BitVec width) :
    wordCmpHOL .less pattern (BitVec.ofNat width 0) = pattern.msb := by
  have positive : 0 < 2 ^ (width - 1) := Nat.pow_pos (by decide)
  simp only [wordCmpHOL, holAsmSignedLess, BitVec.toNat_ofNat, Nat.zero_mod,
    BitVec.msb_eq_decide]
  split <;> simp_all

/-- Local reassociation of the original bitmap prefix. The unconditional
native clock-clamp identity discharges both Seq clamps. -/
theorem sequenceAssoc {width : Nat} [NeZero width] {C F : Type}
    (first second third : HolProg width) (target : StackSemStateFiniteExact width C F) :
    evaluate (.seq first (.seq second third), target) =
      evaluate (.seq (.seq first second) third, target) := by
  rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  rcases run : evaluate (first, target) with ⟨result, post⟩
  cases result
  · exact evaluate_seq second third post |>.trans
      (by rw [StackSemEvaluateClock.fixClockEvaluate])
  · rfl

/-- Native outer-loop exit on a nonnegative bitmap. No clock is consumed. -/
theorem copyWhileExit {width : Nat} [NeZero width] {C F : Type}
    (temporary bitmap : Nat) (pattern : BitVec width)
    (target : StackSemStateFiniteExact width C F)
    (read : getVar 1 target = some (.word pattern))
    (sign : pattern.msb = false) :
    evaluate (whileProg .less 1 (.imm 0)
      (listSeqHOL [copyEach temporary bitmap, loadInst 1 bitmap,
        addBytesInWordInst bitmap]), target) = (none, target) := by
  have comparison : wordCmpHOL .less pattern (0 : BitVec width) = pattern.msb :=
    signedLessZero pattern
  simp only [whileProg, whileHOL]
  rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate]
  simp only [evaluate_ite, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
    read, wordSemWordCmp, comparison, sign]
  simp [evaluate_break, StackSemControl.contLoop, StackSemControl.exitLoop]

/-- The original outer loop reenters after a successful body and one clock
step. The body run is a local intermediate fact derived from CopyEach and
loadBitmapFromHeap by the full source induction. -/
theorem copyWhileReenter {width : Nat} [NeZero width] {C F : Type}
    (temporary bitmap : Nat) (pattern : BitVec width)
    (target post : StackSemStateFiniteExact width C F)
    (read : getVar 1 target = some (.word pattern))
    (sign : pattern.msb = true)
    (clock : post.clock ≠ 0)
    (bodyRun : evaluate
      (listSeqHOL [copyEach temporary bitmap, loadInst 1 bitmap,
        addBytesInWordInst bitmap], target) = (none, post)) :
    evaluate (whileProg .less 1 (.imm 0)
      (listSeqHOL [copyEach temporary bitmap, loadInst 1 bitmap,
        addBytesInWordInst bitmap]), target) =
    evaluate (whileProg .less 1 (.imm 0)
      (listSeqHOL [copyEach temporary bitmap, loadInst 1 bitmap,
        addBytesInWordInst bitmap]), decClock post) := by
  have comparison : wordCmpHOL .less pattern (0 : BitVec width) = pattern.msb :=
    signedLessZero pattern
  simp only [whileProg, whileHOL]
  rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate]
  simp only [evaluate_ite, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
    read, wordSemWordCmp, comparison, sign, bodyRun,
    StackSemControl.contLoop, if_true, clock, if_false]

/-- Reassociate the native CopyLoop prefix into the exact loaded state. -/
theorem copyLoopAfterPrefix {width : Nat} [NeZero width] {C F : Type}
    (temporary bitmap : Nat) (target loaded : StackSemStateFiniteExact width C F)
    (prefixRun : evaluate (listSeqHOL [loadInst 1 bitmap, addBytesInWordInst bitmap],
      target) = (none, loaded)) :
    evaluate (copyLoop temporary bitmap, target) =
      evaluate (.seq (whileProg .less 1 (.imm 0)
        (listSeqHOL [copyEach temporary bitmap, loadInst 1 bitmap,
          addBytesInWordInst bitmap])) (copyEach temporary bitmap), loaded) := by
  simp only [copyLoop, listSeqHOL]
  rw [sequenceAssoc, evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  change evaluate (.seq (loadInst 1 bitmap) (addBytesInWordInst bitmap), target) =
    (none, loaded) at prefixRun
  rw [prefixRun]

/-- Local native nonnegative branch of CopyLoop. This equation composes
with the full accepted CopyEach theorem in the source induction. -/
theorem copyLoopNonnegative {width : Nat} [NeZero width] {C F : Type}
    (temporary bitmap : Nat) (pattern : BitVec width)
    (target loaded : StackSemStateFiniteExact width C F)
    (prefixRun : evaluate (listSeqHOL [loadInst 1 bitmap, addBytesInWordInst bitmap],
      target) = (none, loaded))
    (read : getVar 1 loaded = some (.word pattern))
    (sign : pattern.msb = false) :
    evaluate (copyLoop temporary bitmap, target) =
      evaluate (copyEach temporary bitmap, loaded) := by
  rw [copyLoopAfterPrefix temporary bitmap target loaded prefixRun,
    evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
    copyWhileExit temporary bitmap pattern loaded read sign]


/-- Native recursive branch, factored exactly as the original outer source
recursion. The three intermediate runs and reload under decClock are local
facts derived from the original heap and accepted CopyEach theorem. -/
theorem copyLoopNegative {width : Nat} [NeZero width] {C F : Type}
    (temporary bitmap : Nat) (pattern : BitVec width)
    (target loaded copied next : StackSemStateFiniteExact width C F)
    (prefixRun : evaluate
      (listSeqHOL [loadInst 1 bitmap, addBytesInWordInst bitmap], target) =
      (none, loaded))
    (read : getVar 1 loaded = some (.word pattern))
    (sign : pattern.msb = true)
    (copyRun : evaluate (copyEach temporary bitmap, loaded) = (none, copied))
    (reloadRun : evaluate
      (listSeqHOL [loadInst 1 bitmap, addBytesInWordInst bitmap], copied) =
      (none, next))
    (reloadDecRun : evaluate
      (listSeqHOL [loadInst 1 bitmap, addBytesInWordInst bitmap], decClock copied) =
      (none, decClock next))
    (clock : next.clock ≠ 0) :
    evaluate (copyLoop temporary bitmap, target) =
      evaluate (copyLoop temporary bitmap, decClock copied) := by
  have bodyRun : evaluate
      (listSeqHOL [copyEach temporary bitmap, loadInst 1 bitmap,
        addBytesInWordInst bitmap], loaded) = (none, next) := by
    change evaluate (.seq (copyEach temporary bitmap)
      (listSeqHOL [loadInst 1 bitmap, addBytesInWordInst bitmap]), loaded) = _
    rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, copyRun]
    exact reloadRun
  rw [copyLoopAfterPrefix temporary bitmap target loaded prefixRun,
    copyLoopAfterPrefix temporary bitmap (decClock copied) (decClock next) reloadDecRun]
  rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
    copyWhileReenter temporary bitmap pattern loaded next read sign clock bodyRun]
  rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]


/-- Canonical codec of the actual native state used by this theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original outer bitmap-copy simulation (1334–1471). Native source
induction derives the existential clock allowance, temporary-register
alternative, bitmap pointer and complete framed memory result. The original
unused `i1` binder is retained as `_unusedIndex`. Boolean native domains denote
their true sets. Words and canonical finite maps use only the named reviewed
translations. The evaluator closure inherits the reviewed
reals_as_rational_cuts FP carrier (SOUNDNESS item 8), although this program
executes only integer instructions. No target run or clock law is assumed. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "copy_loop_thm"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem copyLoopThm {width : Nat} [NeZero width] {C F : Type}
    (temporary bitmap index _unusedIndex : Nat)
    (address offset finalAddress base : BitVec width)
    (bitmaps : List (BitVec width))
    (domain targetDomain : BitVec width → Prop) [DecidablePred domain]
    (memory finalMemory : BitVec width → WordLocW width)
    (rest : ((BitVec width × WordLocW width) → Prop) → Prop)
    (target : StackSemStateFiniteExact width C F)
    (hypothesis :
      StackSemStoreConsts.copyWordsExact index address offset bitmaps domain memory =
        some (finalAddress, finalMemory) ∧
      [1, 2, 3, temporary, bitmap].Nodup ∧
      targetDomain = (fun key => target.mdomain key = true) ∧
      goodDimindex width ∧
      (∀ key, domain key → targetDomain key) ∧
      getVar 2 target = some (.word address) ∧
      getVar 3 target = some (.word offset) ∧
      getVar bitmap target =
        some (.word (base + bytesInWord width * BitVec.ofNat width index)) ∧
      SetSep.star
        (SetSep.star (Misc.wordList base (bitmaps.map WordLocW.word)) rest)
        (memoryHOL memory domain) (SetSep.fun2Set (target.memory, targetDomain))) :
    ∃ (allowance : Nat) (unchanged : Bool) (value nextBitmap : BitVec width)
      (nextMemory : BitVec width → WordLocW width),
      evaluate (copyLoop temporary bitmap, {target with clock := target.clock + allowance}) =
        (none, {target with memory := nextMemory, regs := (((if unchanged then target.regs else target.regs.updateEq (temporary, .word value)).updateEq (2, .word finalAddress)).updateEq (1, .word 1)).updateEq (bitmap, .word nextBitmap)}) ∧
      SetSep.star
        (SetSep.star (Misc.wordList base (bitmaps.map WordLocW.word)) rest)
        (memoryHOL finalMemory domain) (SetSep.fun2Set (nextMemory, targetDomain)) := by
  fun_induction StackSemStoreConsts.copyWordsExact index address offset bitmaps domain memory
    generalizing finalAddress finalMemory target
  case case1 => cases hypothesis.1
  case case2 => cases hypothesis.1
  case case3 i a m bound pattern nextIndex nextAddress nextMemory patternRun sign ih =>
    rcases hypothesis with ⟨success, distinct, domainEq, good, subset,
      addressRead, offsetRead, bitmapRead, heap⟩
    have valid : i < bitmaps.length := by omega
    have patternEq : pattern = bitmaps[i] := by simp [pattern, getElem!_pos, valid]
    let loaded := loadBitmapState bitmap i base pattern target
    have reads := loadBitmapReads temporary bitmap i base pattern a offset target
      distinct addressRead offsetRead
    change getVar 1 loaded = _ ∧ getVar 2 loaded = _ ∧ getVar 3 loaded = _ ∧
      getVar bitmap loaded = _ ∧ loaded.clock = target.clock at reads
    obtain ⟨allowance, value, resultMemory, copyRun, copiedHeap⟩ :=
      CopyEachProof.copyEachThm temporary bitmap (i + 1) nextIndex
        pattern a offset nextAddress base bitmaps domain targetDomain m nextMemory rest loaded
        ⟨patternRun, distinct, domainEq, good, reads.1, subset,
          reads.2.1, reads.2.2.1, reads.2.2.2.1, heap⟩
    let copied : StackSemStateFiniteExact width C F :=
      {loaded with memory := resultMemory, regs := (((if pattern = 1 then loaded.regs else loaded.regs.updateEq (temporary, .word value)).updateEq (2, .word nextAddress)).updateEq (1, .word 1)).updateEq (bitmap, .word (base + bytesInWord width * BitVec.ofNat width nextIndex))}
    change evaluate (copyEach temporary bitmap,
      {loaded with clock := loaded.clock + allowance}) = (none, copied) at copyRun
    have bTwo : bitmap ≠ 2 := by
      simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
      omega
    have bThree : bitmap ≠ 3 := by
      simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
      omega
    have tThree : temporary ≠ 3 := by
      simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
      omega
    have copiedReads : getVar 2 copied = some (.word nextAddress) ∧
        getVar 3 copied = some (.word offset) ∧
        getVar bitmap copied = some (.word
          (base + bytesInWord width * BitVec.ofNat width nextIndex)) := by
      change target.regs.lookup 3 = _ at offsetRead
      by_cases sentinel : pattern = BitVec.ofNat width 1 <;>
        simp [copied, loaded, loadBitmapState, getVar, sentinel,
          HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          Ne.symm bTwo, Ne.symm bThree, Ne.symm tThree, offsetRead]
    obtain ⟨recursiveAllowance, unchanged, recursiveValue, nextBitmap,
      finalTargetMemory, recursiveRun, finalHeap⟩ :=
      ih finalAddress finalMemory copied
        ⟨success, distinct, domainEq, good, subset,
          copiedReads.1, copiedReads.2.1, copiedReads.2.2, copiedHeap⟩
    have nextValid : nextIndex < bitmaps.length := by
      by_contra outside
      have outside : bitmaps.length ≤ nextIndex := by omega
      rw [StackSemStoreConsts.copyWordsExact, dif_pos outside] at success
      cases success
    let boosted := {target with clock := target.clock + (allowance + recursiveAllowance + 1)}
    let boostedLoaded := {loaded with clock := loaded.clock + (allowance + recursiveAllowance + 1)}
    let boostedCopied := {copied with clock := copied.clock + (recursiveAllowance + 1)}
    let next := loadBitmapState bitmap nextIndex base bitmaps[nextIndex] boostedCopied
    have firstRun := loadBitmapFromHeap temporary bitmap i base bitmaps domain m rest
      boosted distinct valid bitmapRead (by simpa [domainEq] using heap)
    have firstState : loadBitmapState bitmap i base bitmaps[i] boosted = boostedLoaded := by
      simp only [← patternEq, boosted, boostedLoaded, loaded, loadBitmapState]
    rw [firstState] at firstRun
    have boostedCopyRun := Compiler.Backend.StackProps.evaluateAddClock
      (recursiveAllowance + 1) (copyEach temporary bitmap)
      {loaded with clock := loaded.clock + allowance} none copied ⟨copyRun, by simp⟩
    have boostedCopy : evaluate (copyEach temporary bitmap, boostedLoaded) =
        (none, boostedCopied) := by
      simpa only [boostedLoaded, boostedCopied, Nat.add_assoc] using boostedCopyRun
    have reloadRun : evaluate
        (listSeqHOL [loadInst 1 bitmap, addBytesInWordInst bitmap], boostedCopied) =
        (none, next) :=
      loadBitmapFromHeap temporary bitmap nextIndex base bitmaps domain nextMemory rest
        boostedCopied distinct nextValid copiedReads.2.2
        (by simpa [domainEq, boostedCopied, copied, loaded, loadBitmapState] using copiedHeap)
    have reloadDecRun : evaluate
        (listSeqHOL [loadInst 1 bitmap, addBytesInWordInst bitmap], decClock boostedCopied) =
        (none, decClock next) := by
      have run := loadBitmapFromHeap temporary bitmap nextIndex base bitmaps domain nextMemory rest
        (decClock boostedCopied) distinct nextValid copiedReads.2.2
        (by simpa [domainEq, decClock, boostedCopied, copied, loaded, loadBitmapState] using copiedHeap)
      simpa only [next, loadBitmapState, decClock] using run
    have nonzero : next.clock ≠ 0 := by
      dsimp [next, loadBitmapState, boostedCopied]
      omega
    have loopRun := copyLoopNegative temporary bitmap pattern boosted boostedLoaded
      boostedCopied next firstRun reads.1 sign boostedCopy reloadRun reloadDecRun nonzero
    have reentryState : decClock boostedCopied =
        {copied with clock := copied.clock + recursiveAllowance} := by
      simp [decClock, boostedCopied]
    refine ⟨allowance + recursiveAllowance + 1,
      decide (pattern = 1) && unchanged, (if unchanged then value else recursiveValue),
      nextBitmap, finalTargetMemory, ?_, finalHeap⟩
    change evaluate (copyLoop temporary bitmap, boosted) = _
    rw [loopRun, reentryState, recursiveRun]
    dsimp only [copied, loaded, loadBitmapState]
    congr 2
    apply HolFiniteMapExact.ext_lookup
    intro query
    simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
    have tOne : temporary ≠ 1 := by omega
    have tTwo : temporary ≠ 2 := by omega
    have tb : temporary ≠ bitmap := by omega
    cases unchanged <;>
      by_cases sentinel : pattern = BitVec.ofNat width 1 <;>
      by_cases qBitmap : query = bitmap <;>
      by_cases qOne : query = 1 <;>
      by_cases qTwo : query = 2 <;>
      by_cases qTemporary : query = temporary <;>
      simp [sentinel, qBitmap, qOne, qTwo, qTemporary, tOne, tTwo, tb,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  case case4 i a m bound pattern nextIndex nextAddress nextMemory patternRun sign =>
    rcases hypothesis with ⟨success, distinct, domainEq, good, subset,
      addressRead, offsetRead, bitmapRead, heap⟩
    cases Option.some.inj success
    have valid : i < bitmaps.length := by omega
    have patternEq : pattern = bitmaps[i] := by
      simp [pattern, getElem!_pos, valid]
    let loaded := loadBitmapState bitmap i base pattern target
    have reads := loadBitmapReads temporary bitmap i base pattern a offset target
      distinct addressRead offsetRead
    change getVar 1 loaded = _ ∧ getVar 2 loaded = _ ∧ getVar 3 loaded = _ ∧
      getVar bitmap loaded = _ ∧ loaded.clock = target.clock at reads
    have loadedHeap : SetSep.star
        (SetSep.star (Misc.wordList base (bitmaps.map WordLocW.word)) rest)
        (memoryHOL m domain) (SetSep.fun2Set (loaded.memory, targetDomain)) := heap
    obtain ⟨allowance, value, resultMemory, copyRun, finalHeap⟩ :=
      CopyEachProof.copyEachThm temporary bitmap (i + 1) nextIndex
        pattern a offset nextAddress base bitmaps domain targetDomain m nextMemory rest loaded
        ⟨patternRun, distinct, domainEq, good, reads.1, subset,
          reads.2.1, reads.2.2.1, reads.2.2.2.1, loadedHeap⟩
    have prefixRun := loadBitmapFromHeap temporary bitmap i base bitmaps domain m rest
      {target with clock := target.clock + allowance} distinct valid bitmapRead
      (by simpa [domainEq] using heap)
    have prefixLoaded : loadBitmapState bitmap i base bitmaps[i]
        {target with clock := target.clock + allowance} =
        {loaded with clock := loaded.clock + allowance} := by
      simp only [← patternEq, loaded, loadBitmapState]
    rw [prefixLoaded] at prefixRun
    have nonnegative : pattern.msb = false := by simpa using sign
    have loopRun := copyLoopNonnegative temporary bitmap pattern
      {target with clock := target.clock + allowance}
      {loaded with clock := loaded.clock + allowance} prefixRun reads.1 nonnegative
    refine ⟨allowance, decide (pattern = 1), value,
      base + bytesInWord width * BitVec.ofNat width nextIndex,
      resultMemory, ?_, finalHeap⟩
    rw [loopRun, copyRun]
    dsimp only [loaded, loadBitmapState]
    congr 2
    apply HolFiniteMapExact.ext_lookup
    intro query
    simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
    have tOne : temporary ≠ 1 := by omega
    have tb : temporary ≠ bitmap := by omega
    by_cases sentinel : pattern = BitVec.ofNat width 1 <;>
      by_cases qBitmap : query = bitmap <;>
      by_cases qOne : query = 1 <;>
      by_cases qTwo : query = 2 <;>
      by_cases qTemporary : query = temporary <;>
      simp [sentinel, qBitmap, qOne, qTwo, qTemporary, tOne, tb,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

end Flapjack.Compiler.Backend.StackRemove.CopyLoopProof
