import Flapjack.Compiler.Backend.StackRemove.Proofs.StackHeap
import Flapjack.FiniteMap.MapKeys
import Flapjack.Compiler.Backend.StackRemove.CopyLoop
import Flapjack.Compiler.Backend.Semantics.StackSem.StoreConsts
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef
import Flapjack.Compiler.Backend.StackRemove.Proofs.MemoryWrites
namespace Flapjack.Compiler.Backend.StackRemove.CopyEachProof
open Flapjack StackSemStoreConsts

/-- Local source sentinel equation for the original copy_each induction case;
no independently named HOL declaration is claimed. -/
theorem copyPatternOne {width : Nat} [NeZero width]
    (index : Nat) (address offset : BitVec width) (bitmaps : List (BitVec width))
    (domain : BitVec width → Prop) [DecidablePred domain]
    (memory : BitVec width → WordLocW width) :
    copyWordsForPattern 1 index address offset bitmaps domain memory =
      some (index, address, memory) := by
  simp [copyWordsForPattern, NeZero.ne width]

/-- Local target sentinel equation for the original induction base. The
original register read is the only premise; no clock or memory premise is
required, since the loop body selects Break before its re-entry clock check. -/
theorem copyEachSentinel {width : Nat} [NeZero width] {C F : Type}
    (temporary bitmap : Nat) (target : StackSemStateFiniteExact width C F)
    (read : StackSemStateOps.getVar 1 target = some (.word 1)) :
    StackSemEvaluate.evaluate (copyEach temporary bitmap, target) = (none, target) := by
  simp only [copyEach, Compiler.Backend.StackLang.whileProg,
    Compiler.Backend.StackLang.whileHOL]
  rw [StackSemEvaluate.evaluate_loop]
  simp [StackSemEvaluate.evaluate_ite, StackSemStateOps.getVarImm,
    Encoders.Asm.HolRegImm.toWordRegImm, read,
    wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL,
    StackSemEvaluate.evaluate_break, StackSemControl.fixClock,
    StackSemControl.contLoop, StackSemControl.exitLoop]

/-- Local proof infrastructure for the sentinel post-state register equation:
writing a value already present preserves the entire canonical native state.
No separate HOL declaration is claimed. -/
theorem setVarKnown {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (value : WordLocW width)
    (state : StackSemStateFiniteExact width C F)
    (read : StackSemStateOps.getVar register state = some value) :
    StackSemStateOps.setVar register value state = state := by
  change state.regs.lookup register = some value at read
  have unchanged : state.regs.updateEq (register, value) = state.regs := by
    apply HolFiniteMapExact.ext_lookup
    intro query
    by_cases same : query = register
    · subst query
      simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ite_true, read]
    · simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, same, ite_false]
  simp only [StackSemStateOps.setVar, unchanged]

/-- Local complete sentinel post-state equation. These are precisely the
three original source register reads at pattern=1; no alias or clock premise
is needed to establish that the original repeated updates are identities. -/
theorem sentinelPostState {width : Nat} [NeZero width] {C F : Type}
    (bitmap index : Nat) (base address : BitVec width)
    (target : StackSemStateFiniteExact width C F)
    (oneRead : StackSemStateOps.getVar 1 target = some (.word 1))
    (addressRead : StackSemStateOps.getVar 2 target = some (.word address))
    (bitmapRead : StackSemStateOps.getVar bitmap target =
      some (.word (base + bytesInWord width * BitVec.ofNat width index))) :
    ({target with memory := target.memory, regs := ((target.regs.updateEq (2, .word address)).updateEq (1, .word 1)).updateEq (bitmap, .word (base + bytesInWord width * BitVec.ofNat width index))} : StackSemStateFiniteExact width C F) = target := by
  have addressMap := congrArg (fun state : StackSemStateFiniteExact width C F => state.regs)
    (setVarKnown 2 (.word address) target addressRead)
  have oneMap := congrArg (fun state : StackSemStateFiniteExact width C F => state.regs)
    (setVarKnown 1 (.word 1) target oneRead)
  have bitmapMap := congrArg (fun state : StackSemStateFiniteExact width C F => state.regs)
    (setVarKnown bitmap (.word (base + bytesInWord width * BitVec.ofNat width index)) target bitmapRead)
  change target.regs.updateEq (2, .word address) = target.regs at addressMap
  change target.regs.updateEq (1, .word 1) = target.regs at oneMap
  change target.regs.updateEq
    (bitmap, .word (base + bytesInWord width * BitVec.ofNat width index)) = target.regs at bitmapMap
  simp only [addressMap, oneMap, bitmapMap]

/-- The complete original pattern-one induction conclusion, including source
success inversion, clock allowance, repeated register updates and the framed
memory assertion. This local case is not the full recursive HOL theorem. -/
theorem copyEachPatternOne {width : Nat} [NeZero width] {C F : Type}
    (temporary bitmap index finalIndex : Nat)
    (address offset finalAddress base : BitVec width)
    (bitmaps : List (BitVec width))
    (domain targetDomain : BitVec width → Prop) [DecidablePred domain]
    (memory finalMemory : BitVec width → WordLocW width)
    (rest : ((BitVec width × WordLocW width) → Prop) → Prop)
    (target : StackSemStateFiniteExact width C F)
    (hypothesis :
      copyWordsForPattern 1 index address offset bitmaps domain memory =
        some (finalIndex, finalAddress, finalMemory) ∧
      [1, 2, 3, temporary, bitmap].Nodup ∧
      (∀ key, targetDomain key ↔ target.mdomain key = true) ∧
      goodDimindex width ∧
      StackSemStateOps.getVar 1 target = some (.word 1) ∧
      (∀ key, domain key → targetDomain key) ∧
      StackSemStateOps.getVar 2 target = some (.word address) ∧
      StackSemStateOps.getVar 3 target = some (.word offset) ∧
      StackSemStateOps.getVar bitmap target =
        some (.word (base + bytesInWord width * BitVec.ofNat width index)) ∧
      SetSep.star
        (SetSep.star (Misc.wordList base (bitmaps.map WordLocW.word)) rest)
        (memoryHOL memory domain) (SetSep.fun2Set (target.memory, targetDomain))) :
    ∃ (allowance : Nat) (_value : BitVec width) (nextMemory : BitVec width → WordLocW width),
      StackSemEvaluate.evaluate
        (copyEach temporary bitmap, {target with clock := target.clock + allowance}) =
        (none, {target with memory := nextMemory, regs := ((target.regs.updateEq (2, .word finalAddress)).updateEq (1, .word 1)).updateEq (bitmap, .word (base + bytesInWord width * BitVec.ofNat width finalIndex))}) ∧
      SetSep.star
        (SetSep.star (Misc.wordList base (bitmaps.map WordLocW.word)) rest)
        (memoryHOL finalMemory domain) (SetSep.fun2Set (nextMemory, targetDomain)) := by
  rcases hypothesis with ⟨success, _distinct, _domain, _good,
    oneRead, _subset, addressRead, _offsetRead, bitmapRead, heap⟩
  rw [copyPatternOne] at success
  cases success
  refine ⟨0, 0, target.memory, ?_, heap⟩
  simp only [Nat.add_zero]
  rw [sentinelPostState bitmap index base address target oneRead addressRead bitmapRead]
  exact copyEachSentinel temporary bitmap target oneRead

/-- The original recursive source index guard and full separated heap derive
the actual native bitmap load. No target read or successful execution is assumed. -/
theorem bitmapLoad {width : Nat} [NeZero width] {C F : Type}
    (base : BitVec width) (bitmaps : List (BitVec width)) (index : Nat)
    (domain : BitVec width → Prop) (memory : BitVec width → WordLocW width)
    (rest : ((BitVec width × WordLocW width) → Prop) → Prop)
    (target : StackSemStateFiniteExact width C F)
    (bound : index < bitmaps.length)
    (heap : SetSep.star
      (SetSep.star (Misc.wordList base (bitmaps.map WordLocW.word)) rest)
      (memoryHOL memory domain)
      (SetSep.fun2Set (target.memory, fun key => target.mdomain key = true))) :
    StackSemStateOps.memLoad
      (base + bytesInWord width * BitVec.ofNat width index) target =
      some (.word bitmaps[index]) := by
  rcases heap with ⟨listFrame, memoryHeap, outerSplit, listFrameAssertion, _memoryAssertion⟩
  rcases listFrameAssertion with ⟨listHeap, frameHeap, innerSplit, listAssertion, _frameAssertion⟩
  have mappedBound : index < (bitmaps.map WordLocW.word).length := by simpa using bound
  have member := StackHeap.wordListNth base (bitmaps.map WordLocW.word)
    listHeap index mappedBound listAssertion
  have graph : SetSep.fun2Set (target.memory, fun key => target.mdomain key = true)
      (base + bytesInWord width * BitVec.ofNat width index, .word bitmaps[index]) := by
    rw [← outerSplit.1]
    apply Or.inl
    rw [← innerSplit.1]
    apply Or.inl
    simpa only [List.getElem_map] using member
  have facts := (SetSep.fun2SetThm target.memory
    (fun key => target.mdomain key = true)
    (base + bytesInWord width * BitVec.ofNat width index) (.word bitmaps[index])).mp graph
  simp only [StackSemStateOps.memLoad, facts.1, facts.2, ite_true]

/-- The original bit-zero relocation test, on the same positive-width word
carrier used by source bitmap copying and native instruction comparison. -/
theorem relocationTest {width : Nat} [NeZero width] (pattern : BitVec width) :
    Compiler.Encoders.Asm.wordCmpHOL .test pattern (BitVec.ofNat width 1) = !(pattern.getLsbD 0) := by
  simp only [Compiler.Encoders.Asm.wordCmpHOL]
  change ((pattern &&& BitVec.ofNat width 1) == (0 : BitVec width)) = !(pattern.getLsbD 0)
  rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  cases pattern.getLsbD 0 <;> simp [BitVec.ofBool, BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (by decide : 0 < 1), NeZero.ne width]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Native execution of the original six-instruction recursive copy body.
All reads and domain membership are explicit local facts to be derived from
original source premises by the assembling induction. This is infrastructure,
not a replacement statement for the full HOL simulation theorem. -/
theorem copyBodyRun {width : Nat} [NeZero width] {C F : Type}
    (temporary bitmap : Nat) (pattern address offset bitmapAddress value : BitVec width)
    (target : StackSemStateFiniteExact width C F)
    (distinct : [1, 2, 3, temporary, bitmap].Nodup)
    (good : goodDimindex width)
    (patternRead : StackSemStateOps.getVar 1 target = some (.word pattern))
    (addressRead : StackSemStateOps.getVar 2 target = some (.word address))
    (offsetRead : StackSemStateOps.getVar 3 target = some (.word offset))
    (bitmapRead : StackSemStateOps.getVar bitmap target = some (.word bitmapAddress))
    (loadRead : StackSemStateOps.memLoad bitmapAddress target = some (.word value))
    (storeDomain : target.mdomain address = true) :
    let copied := if Compiler.Encoders.Asm.wordCmpHOL .test pattern 1 then value else value + offset
    StackSemEvaluate.evaluate
      (Compiler.Backend.StackLang.listSeqHOL [loadInst temporary bitmap,
        Compiler.Backend.StackLang.addBytesInWordInst bitmap,
        .ite .test 1 (.imm 1) .skip (Compiler.Backend.StackLang.addInst temporary 3),
        rightShiftInst 1 1, storeInst temporary 2,
        Compiler.Backend.StackLang.addBytesInWordInst 2], target) =
      (none, {target with memory := fun key => if key = address then .word copied else target.memory key, regs := (((target.regs.updateEq (temporary, .word copied)).updateEq (bitmap, .word (bitmapAddress + bytesInWord width))).updateEq (1, .word (pattern >>> (1 : Nat)))).updateEq (2, .word (address + bytesInWord width))}) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or] at distinct
  simp only [StackSemStateOps.getVar] at patternRead addressRead offsetRead bitmapRead
  have wide : 1 < width := by rcases good with h | h <;> omega
  have tOne : temporary ≠ 1 := by omega
  have tTwo : temporary ≠ 2 := by omega
  have tThree : temporary ≠ 3 := by omega
  have bOne : bitmap ≠ 1 := by omega
  have bTwo : bitmap ≠ 2 := by omega
  have bThree : bitmap ≠ 3 := by omega
  have tb : temporary ≠ bitmap := by omega
  have bt : bitmap ≠ temporary := by omega
  have oneNat : (BitVec.ofNat width 1).toNat = 1 := by simp [show 0 < width by omega]
  cases testResult : Compiler.Encoders.Asm.wordCmpHOL .test pattern (BitVec.ofNat width 1) <;>
    simp [testResult, Compiler.Backend.StackLang.listSeqHOL, loadInst, storeInst, rightShiftInst,
    Compiler.Backend.StackLang.addBytesInWordInst, Compiler.Backend.StackLang.addInst,
    StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_inst,
    StackSemEvaluate.evaluate_ite, StackSemEvaluate.evaluate_skip,
    StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    StackSemExpressions.assign, StackSemExpressions.wordExp,
    StackSemStateOps.getVar, StackSemStateOps.getVarImm,
    Encoders.Asm.HolRegImm.toWordRegImm, StackSemStateOps.setVar,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    StackSemControl.fixClock, wordSemWordCmp,
    wordOpHOL, wordOp, wordShiftHOL, oneNat, Nat.not_le.mpr wide,
    patternRead, addressRead, offsetRead, bitmapRead,
    tOne, tTwo, tThree, bOne, bTwo, bThree, tb, bt, Ne.symm tOne, Ne.symm tTwo, Ne.symm tThree, Ne.symm bOne, Ne.symm bTwo, Ne.symm bThree, loadRead, StackSemStateOps.memStore, storeDomain,
    wordSemBytesInWord, bytesInWord]
  all_goals
    apply HolFiniteMapExact.ext_lookup
    intro query
    by_cases same : query = temporary
    · subst query
      simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, tb, tOne, tTwo]
    · simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, same]

/-- Exact intermediate state after one original bitmap-bit iteration.
Local factoring only; the source memory update uses the same relocated word. -/
def copyStepState {width : Nat} [NeZero width] {C F : Type}
    (temporary bitmap index : Nat) (pattern address offset base value : BitVec width)
    (target : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  let copied := if pattern.getLsbD 0 then value + offset else value
  {target with memory := fun key => if key = address then .word copied else target.memory key, regs := (((target.regs.updateEq (temporary, .word copied)).updateEq (bitmap, .word (base + bytesInWord width * BitVec.ofNat width index + bytesInWord width))).updateEq (1, .word (pattern >>> (1 : Nat)))).updateEq (2, .word (address + bytesInWord width))}

/-- One original recursive iteration derives the native body execution and
full source/target memory frame together. Its bounded index and source-domain
membership are the actual successful copy_words_for_pattern branch guards;
no target read, target-domain or target-execution premise is supplied. -/
theorem copyStepFromHeap {width : Nat} [NeZero width] {C F : Type}
    (temporary bitmap index : Nat) (pattern address offset base : BitVec width)
    (bitmaps : List (BitVec width)) (domain : BitVec width → Prop)
    (memory : BitVec width → WordLocW width)
    (rest : ((BitVec width × WordLocW width) → Prop) → Prop)
    (target : StackSemStateFiniteExact width C F)
    (distinct : [1, 2, 3, temporary, bitmap].Nodup)
    (good : goodDimindex width)
    (patternRead : StackSemStateOps.getVar 1 target = some (.word pattern))
    (addressRead : StackSemStateOps.getVar 2 target = some (.word address))
    (offsetRead : StackSemStateOps.getVar 3 target = some (.word offset))
    (bitmapRead : StackSemStateOps.getVar bitmap target =
      some (.word (base + bytesInWord width * BitVec.ofNat width index)))
    (guard : domain address ∧ index < bitmaps.length)
    (subset : ∀ key, domain key → target.mdomain key = true)
    (heap : SetSep.star
      (SetSep.star (Misc.wordList base (bitmaps.map WordLocW.word)) rest)
      (memoryHOL memory domain)
      (SetSep.fun2Set (target.memory, fun key => target.mdomain key = true))) :
    let value := bitmaps[index]'guard.2
    let copied := if pattern.getLsbD 0 then value + offset else value
    let post := copyStepState temporary bitmap index pattern address offset base value target
    StackSemEvaluate.evaluate
      (Compiler.Backend.StackLang.listSeqHOL [loadInst temporary bitmap,
        Compiler.Backend.StackLang.addBytesInWordInst bitmap,
        .ite .test 1 (.imm 1) .skip (Compiler.Backend.StackLang.addInst temporary 3),
        rightShiftInst 1 1, storeInst temporary 2,
        Compiler.Backend.StackLang.addBytesInWordInst 2], target) = (none, post) ∧
      SetSep.star
        (SetSep.star (Misc.wordList base (bitmaps.map WordLocW.word)) rest)
        (memoryHOL (fun key => if key = address then .word copied else memory key) domain)
        (SetSep.fun2Set (post.memory, fun key => post.mdomain key = true)) := by
  dsimp only
  constructor
  · have run := copyBodyRun temporary bitmap pattern address offset
      (base + bytesInWord width * BitVec.ofNat width index) bitmaps[index] target
      distinct good patternRead addressRead offsetRead bitmapRead
      (bitmapLoad base bitmaps index domain memory rest target guard.2 heap)
      (subset address guard.1)
    cases bit : pattern.getLsbD 0 <;> simpa [relocationTest, copyStepState, bit] using run
  · have swapped : SetSep.star (memoryHOL memory domain)
        (SetSep.star (Misc.wordList base (bitmaps.map WordLocW.word)) rest)
        (SetSep.fun2Set (target.memory, fun key => target.mdomain key = true)) := by
      rw [SetSep.starComm]
      exact heap
    have updated := MemoryWrites.memoryWrite memory target.memory domain
      (fun key => target.mdomain key = true)
      (SetSep.star (Misc.wordList base (bitmaps.map WordLocW.word)) rest)
      address (.word (if pattern.getLsbD 0 then bitmaps[index] + offset else bitmaps[index]))
      ⟨guard.1, subset address guard.1, swapped⟩
    rw [SetSep.starComm] at updated
    dsimp only [copyStepState]
    convert updated using 1
    congr 3
    funext key
    by_cases same : key = address <;> simp [same]
    funext entry
    rcases entry with ⟨key, payload⟩
    by_cases same : key = address <;> simp [SetSep.fun2SetThm, same]

set_option linter.unusedSimpArgs false in
/-- Exact original induction re-entry register facts and clock preservation,
derived from the native iteration post-state rather than supplied as premises. -/
theorem copyStepReads {width : Nat} [NeZero width] {C F : Type}
    (temporary bitmap index : Nat) (pattern address offset base value : BitVec width)
    (target : StackSemStateFiniteExact width C F)
    (distinct : [1, 2, 3, temporary, bitmap].Nodup)
    (offsetRead : StackSemStateOps.getVar 3 target = some (.word offset)) :
    let post := copyStepState temporary bitmap index pattern address offset base value target
    StackSemStateOps.getVar 1 post = some (.word (pattern >>> (1 : Nat))) ∧
    StackSemStateOps.getVar 2 post = some (.word (address + bytesInWord width)) ∧
    StackSemStateOps.getVar 3 post = some (.word offset) ∧
    StackSemStateOps.getVar bitmap post =
      some (.word (base + bytesInWord width * BitVec.ofNat width (index + 1))) ∧
    post.clock = target.clock := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or] at distinct
  have tThree : temporary ≠ 3 := by omega
  have bOne : bitmap ≠ 1 := by omega
  have bTwo : bitmap ≠ 2 := by omega
  have bThree : bitmap ≠ 3 := by omega
  have tOne : temporary ≠ 1 := by omega
  have tTwo : temporary ≠ 2 := by omega
  have addressEq : base + bytesInWord width * BitVec.ofNat width index + bytesInWord width =
      base + bytesInWord width * BitVec.ofNat width (index + 1) := by
    simp [BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]
  simpa [copyStepState, StackSemStateOps.getVar, HolFiniteMapExact.lookup_updateEq,
    FUPDATE_HOL, tThree, bOne, bTwo, bThree, tOne, tTwo,
    Ne.symm tThree, Ne.symm bOne, Ne.symm bTwo, Ne.symm bThree,
    Ne.symm tOne, Ne.symm tTwo, addressEq] using offsetRead

/-- Local loop equation used after the preceding native body proof. The body
run and clock equality are derived by copyStepFromHeap/copyStepReads in the
original induction; they are not hypotheses of the eventual HOL theorem. -/
theorem copyEachReenter {width : Nat} [NeZero width] {C F : Type}
    (temporary bitmap : Nat) (pattern : BitVec width)
    (target post : StackSemStateFiniteExact width C F)
    (patternRead : StackSemStateOps.getVar 1 target = some (.word pattern))
    (notSentinel : pattern ≠ 1)
    (clock : target.clock ≠ 0)
    (postClock : post.clock = target.clock)
    (bodyRun : StackSemEvaluate.evaluate
      (Compiler.Backend.StackLang.listSeqHOL [loadInst temporary bitmap,
        Compiler.Backend.StackLang.addBytesInWordInst bitmap,
        .ite .test 1 (.imm 1) .skip (Compiler.Backend.StackLang.addInst temporary 3),
        rightShiftInst 1 1, storeInst temporary 2,
        Compiler.Backend.StackLang.addBytesInWordInst 2], target) = (none, post)) :
    StackSemEvaluate.evaluate (copyEach temporary bitmap, target) =
      StackSemEvaluate.evaluate (copyEach temporary bitmap, StackSemStateOps.decClock post) := by
  have unclamped : StackSemControl.fixClock target ((none : Option (StackSemResult width)), post) =
      (none, post) := by
    simp only [StackSemControl.fixClock]
    rw [← postClock]
    simp
  simp only [copyEach, Compiler.Backend.StackLang.whileProg,
    Compiler.Backend.StackLang.whileHOL]
  rw [StackSemEvaluate.evaluate_loop]
  simp only [StackSemEvaluate.evaluate_ite, StackSemStateOps.getVarImm,
    Encoders.Asm.HolRegImm.toWordRegImm, patternRead, wordSemWordCmp,
    Compiler.Encoders.Asm.wordCmpHOL]
  change pattern ≠ BitVec.ofNat width 1 at notSentinel
  have comparison : (pattern == (1 : BitVec width)) = false := by simp [notSentinel]
  rw [comparison]
  simp only [Bool.not_false, bodyRun, unclamped, StackSemControl.contLoop,
    if_true, postClock, clock, if_false]

/-- Canonical codec for the actual imported native state; local infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

set_option maxHeartbeats 1000000 in
/-- Full original bitmap-copy simulation. Retains source copy success, distinct
registers, domain equality/inclusion, good word dimension, every register read
and the full separated list/frame/memory assertion. Native execution, total
extra clock, memory frame and both final-register alternatives are derived by
the original pattern induction. Boolean native domains denote their true sets;
words and canonical finite maps use only the named reviewed translations.
The native evaluator closure inherits the reviewed reals_as_rational_cuts FP real carrier (SOUNDNESS
item 8), although this copy body executes only integer instructions. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "copy_each_thm"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem copyEachThm {width : Nat} [NeZero width] {C F : Type}
    (temporary bitmap index finalIndex : Nat)
    (pattern address offset finalAddress base : BitVec width)
    (bitmaps : List (BitVec width))
    (domain targetDomain : BitVec width → Prop) [DecidablePred domain]
    (memory finalMemory : BitVec width → WordLocW width)
    (rest : ((BitVec width × WordLocW width) → Prop) → Prop)
    (target : StackSemStateFiniteExact width C F)
    (hypothesis :
      copyWordsForPattern pattern index address offset bitmaps domain memory =
        some (finalIndex, finalAddress, finalMemory) ∧
      [1, 2, 3, temporary, bitmap].Nodup ∧
      targetDomain = (fun key => target.mdomain key = true) ∧
      goodDimindex width ∧
      StackSemStateOps.getVar 1 target = some (.word pattern) ∧
      (∀ key, domain key → targetDomain key) ∧
      StackSemStateOps.getVar 2 target = some (.word address) ∧
      StackSemStateOps.getVar 3 target = some (.word offset) ∧
      StackSemStateOps.getVar bitmap target =
        some (.word (base + bytesInWord width * BitVec.ofNat width index)) ∧
      SetSep.star
        (SetSep.star (Misc.wordList base (bitmaps.map WordLocW.word)) rest)
        (memoryHOL memory domain) (SetSep.fun2Set (target.memory, targetDomain))) :
    ∃ (allowance : Nat) (_value : BitVec width) (nextMemory : BitVec width → WordLocW width),
      StackSemEvaluate.evaluate
        (copyEach temporary bitmap, {target with clock := target.clock + allowance}) =
        (none, {target with memory := nextMemory, regs := (((if pattern = 1 then target.regs else target.regs.updateEq (temporary, .word _value)).updateEq (2, .word finalAddress)).updateEq (1, .word 1)).updateEq (bitmap, .word (base + bytesInWord width * BitVec.ofNat width finalIndex))}) ∧
      SetSep.star
        (SetSep.star (Misc.wordList base (bitmaps.map WordLocW.word)) rest)
        (memoryHOL finalMemory domain) (SetSep.fun2Set (nextMemory, targetDomain)) := by
  fun_induction copyWordsForPattern pattern index address offset bitmaps domain memory
    generalizing finalIndex finalAddress finalMemory target
  case case1 => cases hypothesis.1
  case case2 index address memory hzero =>
    rcases hypothesis with ⟨success, _distinct, _domain, _good,
      oneRead, _subset, addressRead, _offsetRead, bitmapRead, heap⟩
    cases success
    refine ⟨0, 0, target.memory, ?_, heap⟩
    simp only [Nat.add_zero, ite_true]
    rw [sentinelPostState bitmap index base address target oneRead addressRead bitmapRead]
    exact copyEachSentinel temporary bitmap target oneRead
  case case4 => cases hypothesis.1
  case case3 pattern index address memory hzero hone guard value nextMemory ih =>
    rcases hypothesis with ⟨success, distinct, domainEq, good,
      patternRead, subset, addressRead, offsetRead, bitmapRead, heap⟩
    have canonicalHeap := heap
    rw [domainEq] at canonicalHeap
    have canonicalSubset := subset
    rw [domainEq] at canonicalSubset
    let post := copyStepState temporary bitmap index pattern address offset base value target
    have step := copyStepFromHeap temporary bitmap index pattern address offset base
      bitmaps domain memory rest target distinct good patternRead addressRead offsetRead
      bitmapRead guard canonicalSubset canonicalHeap
    obtain ⟨nextPatternRead, nextAddressRead, nextOffsetRead, nextBitmapRead, nextClock⟩ :=
      copyStepReads temporary bitmap index pattern address offset base value target distinct offsetRead
    have memoryEq : nextMemory =
        (fun key => if key = address then
          .word (if pattern.getLsbD 0 then value + offset else value) else memory key) := by
      funext key
      by_cases same : key = address <;>
        by_cases bit : pattern.getLsbD 0 = true <;> simp [nextMemory, same, bit]
    have nextHeap : SetSep.star
        (SetSep.star (Misc.wordList base (bitmaps.map WordLocW.word)) rest)
        (memoryHOL nextMemory domain) (SetSep.fun2Set (post.memory, targetDomain)) := by
      simpa only [memoryEq, post, value, copyStepState, domainEq] using step.2
    obtain ⟨allowance, finalValue, resultMemory, recursiveRun, finalHeap⟩ :=
      ih finalIndex finalAddress finalMemory post
        ⟨success, distinct, domainEq, good, nextPatternRead, subset,
          by simpa only [bytesInWord] using nextAddressRead,
          nextOffsetRead, nextBitmapRead, nextHeap⟩
    let boosted : StackSemStateFiniteExact width C F :=
      {target with clock := target.clock + (allowance + 1)}
    let boostedPost : StackSemStateFiniteExact width C F :=
      {post with clock := target.clock + (allowance + 1)}
    have boostedStep := copyStepFromHeap temporary bitmap index pattern address offset base
      bitmaps domain memory rest boosted distinct good patternRead addressRead offsetRead
      bitmapRead guard canonicalSubset canonicalHeap
    have boostedRun : StackSemEvaluate.evaluate
        (Compiler.Backend.StackLang.listSeqHOL [loadInst temporary bitmap,
          Compiler.Backend.StackLang.addBytesInWordInst bitmap,
          .ite .test 1 (.imm 1) .skip (Compiler.Backend.StackLang.addInst temporary 3),
          rightShiftInst 1 1, storeInst temporary 2,
          Compiler.Backend.StackLang.addBytesInWordInst 2], boosted) = (none, boostedPost) := by
      simpa only [boosted, boostedPost, post, copyStepState, value] using boostedStep.1
    have reentry := copyEachReenter temporary bitmap pattern boosted boostedPost
      patternRead hone (by dsimp [boosted]; omega) rfl boostedRun
    have reentryState : StackSemStateOps.decClock boostedPost =
        {post with clock := post.clock + allowance} := by
      simp [StackSemStateOps.decClock, boostedPost, post, copyStepState]
    refine ⟨allowance + 1,
      (if pattern >>> (1 : Nat) = 1 then
        (if pattern.getLsbD 0 then value + offset else value) else finalValue),
      resultMemory, ?_, finalHeap⟩
    change StackSemEvaluate.evaluate (copyEach temporary bitmap, boosted) = _
    rw [reentry, reentryState, recursiveRun]
    simp only [hone, if_false, post, copyStepState]
    congr 2
    apply HolFiniteMapExact.ext_lookup
    intro query
    simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
    have tOne : temporary ≠ 1 := by omega
    have tTwo : temporary ≠ 2 := by omega
    have tb : temporary ≠ bitmap := by omega
    by_cases nextSentinel : pattern >>> (1 : Nat) = BitVec.ofNat width 1 <;>
      by_cases qBitmap : query = bitmap <;>
      by_cases qOne : query = 1 <;>
      by_cases qTwo : query = 2 <;>
      by_cases qTemporary : query = temporary <;>
      simp [nextSentinel, qBitmap, qOne, qTwo, qTemporary, tOne, tTwo, tb,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

end Flapjack.Compiler.Backend.StackRemove.CopyEachProof
