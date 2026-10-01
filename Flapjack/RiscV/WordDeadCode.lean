import Flapjack.RiscV.AllocatorMemoryInvariant
import Flapjack.Compiler.Backend.WordAlloc.LivenessRoute
import Flapjack.NatDedup
import Flapjack.RiscV.CakeRegAlloc
import Flapjack.RiscV.WordCse
import Flapjack.RiscV.WordCopyProp

/-!
# Word dead-program elimination

Cake runs `remove_dead_prog` after full SSA and before register allocation.
The port keeps the same boundary explicit here: pure definitions, moves, and
loads whose destinations are not live are removed, while stores, calls, FFI,
and the other effectful Word operations are retained.  The loop rule is
conservative, matching Cake's loop barrier by restarting the body analysis
from the loop's live-in set.
-/

namespace Flapjack.RiscV

open Flapjack

/-- `(live ++ reads).eraseDups`.  The live set is as long as the function, and
    this runs once per statement, so the quadratic `List.eraseDups` made a
    single dead-code pass cubic in function size; `natEraseDups` returns the
    same list. -/
def wordDeadAddReads (live : List Nat) (reads : List Nat) : List Nat :=
  natEraseDupsAppend live reads

def wordDeadRemoveWrites (live : List Nat) (writes : List Nat) : List Nat :=
  live.filter (fun name => name ∉ writes)

def wordDeadCallLive (cutsets : List Nat × List Nat) (arguments : List Nat) : List Nat :=
  wordDeadAddReads [] (cutsets.1 ++ cutsets.2 ++ arguments)

/-! Cake's `remove_dead (Move pri ls)` keeps the priority of the surviving
    moves.  The priority orders the coalescing worklist (`sort_moves` sorts
    descending and `do_coalesce` consumes the first compatible move), so the
    `Move1` SSA entry/ABI shuffle must stay priority 1 for the parameters to
    coalesce onto the ABI registers. -/
def wordDeadMove (priority : Nat) (live : List Nat) (moves : List (Nat × Nat)) :
    WordProg α × List Nat :=
  let kept := moves.filter (fun move => move.1 ∈ live)
  if kept.isEmpty then
    (.skip, live)
  else
    (.move priority kept,
      wordDeadAddReads
        (wordDeadRemoveWrites live (kept.map Prod.fst))
        (kept.map Prod.snd))

def wordDeadInst {α : Type} (live : List Nat) (instruction : WordInst α) :
    WordProg α × List Nat :=
  if WordAlloc.removeDeadInstExecutable instruction (WordAlloc.numSetToExact live) then
    (.skip, live)
  else
    (.inst instruction, wordInstLiveBefore instruction live)

def wordDeadReturnLabels : WordProg α → List Nat
  | .return label _ => [label]
  | .seq first second => wordDeadReturnLabels first ++ wordDeadReturnLabels second
  | .ite _ _ _ thenBranch elseBranch =>
      wordDeadReturnLabels thenBranch ++ wordDeadReturnLabels elseBranch
  | .loop _ body _ | .mustTerminate body => wordDeadReturnLabels body
  | .call none _ _ none => []
  | .call (some (_, _, returnCode, _, _)) _ _ none =>
      wordDeadReturnLabels returnCode
  | .call none _ _ (some (_, body, _, _)) =>
      wordDeadReturnLabels body
  | .call (some (_, _, returnCode, _, _)) _ _ (some (_, body, _, _)) =>
      wordDeadReturnLabels returnCode ++ wordDeadReturnLabels body
  | _ => []

def wordDeadCodeAuxWithLabels : WordProg α → List Nat → List (List Nat × List Nat) →
    List Nat → WordProg α × List Nat
  | .skip, live, _, _ => (.skip, live)
  | .move priority moves, live, _, _ => wordDeadMove priority live moves
  | .assign destination value, live, _, _ =>
      if destination ∈ live then
        (.assign destination value,
          wordDeadAddReads (wordDeadRemoveWrites live [destination])
            (WordAlloc.liveExpressionKeys value))
      else
        (.skip, live)
  | .inst instruction, live, _, _ => wordDeadInst live instruction
  | .get destination store, live, _, _ =>
      if destination ∈ live then
        (.get destination store,
          wordDeadAddReads (wordDeadRemoveWrites live [destination]) [])
      else
        (.skip, live)
  | .store address value, live, _, _ =>
      (.store address value,
        wordDeadAddReads live (WordAlloc.liveExpressionKeys address ++ [value]))
  | .set store value, live, _, _ =>
      (.set store value, wordDeadAddReads live (WordAlloc.liveExpressionKeys value))
  | .seq first second, live, frames, returnLabels =>
      let (second', live) := wordDeadCodeAuxWithLabels second live frames returnLabels
      let (first', live) := wordDeadCodeAuxWithLabels first live frames returnLabels
      (match first', second' with
       | .skip, program => program
       | program, .skip => program
       | _, _ => .seq first' second', live)
  | .ite operator condition right thenBranch elseBranch, live, frames, returnLabels =>
      let (then', thenLive) := wordDeadCodeAuxWithLabels thenBranch live frames returnLabels
      let (else', elseLive) := wordDeadCodeAuxWithLabels elseBranch live frames returnLabels
      let rightReads := match right with
        | .imm _ => []
        | .reg name => [name]
      let live := wordDeadAddReads (thenLive ++ elseLive) (condition :: rightReads)
      match then', else' with
      | .skip, .skip => (.skip, live)
      | _, _ => (.ite operator condition right then' else', live)
  | .loop liveIn body liveOut, _live, frames, returnLabels =>
      let (body', _) := wordDeadCodeAuxWithLabels body liveIn
        ((liveIn, liveOut) :: frames) returnLabels
      (.loop liveIn body' liveOut, liveIn)
  | .mustTerminate body, live, frames, returnLabels =>
      let (body', live) := wordDeadCodeAuxWithLabels body live frames returnLabels
      (.mustTerminate body', live)
  | .break label, _live, frames, _ =>
      (.break label, (wordClashTreeFindLoopFrame label frames).map Prod.snd |>.getD [])
  | .continue label, _live, frames, _ =>
      (.continue label, (wordClashTreeFindLoopFrame label frames).map Prod.fst |>.getD [])
  | .raise exception, live, _, _returnLabels =>
      /- Cake's `get_live (Raise num)` preserves the incoming live set and
         adds only the exception value.  In particular it does not filter
         live names by the function's return labels; doing that changes the
         liveness of values copied through a call continuation and diverges
         from `word_allocScript.sml:get_live_def`. -/
      (.raise exception, wordDeadAddReads live [exception])
  | .return label values, live, _, _ =>
      (.return label values, wordDeadAddReads (label :: live) values)
  | .tick, live, _, _ => (.tick, live)
  | .locValue destination source, live, _, _ =>
      if destination ∈ live then
        (.locValue destination source,
          wordDeadAddReads (wordDeadRemoveWrites live [destination]) [])
      else
        (.skip, live)
  | .call (some (destinations, cutsets, returnCode, returnLabel, entryLabel))
      target arguments handler, live, frames, returnLabels =>
      let (returnCode', _) := wordDeadCodeAuxWithLabels returnCode live frames returnLabels
      let handler' := match handler with
        | none => none
        | some (exception, body, handlerLabel, handlerEntryLabel) =>
            some (exception, (wordDeadCodeAuxWithLabels body live frames []).1,
              handlerLabel, handlerEntryLabel)
      (.call (some (destinations, cutsets, returnCode', returnLabel, entryLabel))
          target arguments handler',
        wordDeadCallLive cutsets arguments)
  | .call returns target arguments handler, _live, _, _ =>
      (.call returns target arguments handler,
        /- Cake's `get_live (Call NONE ...)` is the argument set only.
           In particular, it does not inspect an unreachable handler or
           continuation, and it does not carry the incoming live set across
           a tail call (`word_allocScript.sml:832-834`). -/
        wordDeadAddReads [] arguments)
  | .alloc destination cutsets, _live, _, _ =>
      (.alloc destination cutsets,
        /- Cake's `get_live (Alloc ...)` keeps the allocation result live and
           adds both cut-set components, but does not retain the incoming
           live set (`word_allocScript.sml:802-803`). -/
        wordDeadAddReads [destination] (cutsets.1 ++ cutsets.2))
  | .storeConsts source bitmap codeLength dataLength constants, live, _, _ =>
      (.storeConsts source bitmap codeLength dataLength constants,
        /- `StoreConsts` consumes source and bitmap but produces the code and
           data lengths; this is the exact `get_live` equation rather than a
           conservative read inventory. -/
        wordDeadAddReads (wordDeadRemoveWrites live [source, bitmap])
          [codeLength, dataLength])
  | .opCurrHeap operator destination source, live, _, _ =>
      if destination ∈ live then
        (.opCurrHeap operator destination source,
          wordDeadAddReads (wordDeadRemoveWrites live [destination]) [source])
      else
        (.skip, live)
  | .install codeBuffer codeLength dataBuffer dataLength cutsets, _live, _, _ =>
      (.install codeBuffer codeLength dataBuffer dataLength cutsets,
        /- Cake's `get_live (Install ...)` retains only the four installed
           values and the two cut-set components, not the incoming live set
           (`word_allocScript.sml:805-807`). -/
        wordDeadAddReads [codeBuffer, codeLength, dataBuffer, dataLength]
          (cutsets.1 ++ cutsets.2))
  | .codeBufferWrite address value, live, _, _ =>
      (.codeBufferWrite address value, wordDeadAddReads live [address, value])
  | .dataBufferWrite address value, live, _, _ =>
      (.dataBufferWrite address value, wordDeadAddReads live [address, value])
  | .ffi function configuration configurationLength array arrayLength liveSet, _live, _, _ =>
      (.ffi function configuration configurationLength array arrayLength liveSet,
        /- Cake's `get_live (FFI ...)` likewise starts from the four FFI
           operands and the cut-set components (`word_allocScript.sml:812-815`). -/
        wordDeadAddReads [configuration, configurationLength, array, arrayLength]
          (liveSet.1 ++ liveSet.2))
  | .shareInst operator name address, live, _, _ =>
      match operator with
      | .load | .load8 | .load16 | .load32 =>
          /- Cake deliberately retains ShareInst loads: even a dead load
             emits the observable shared-memory event used by the FFI model. -/
          (.shareInst operator name address,
            wordDeadAddReads (wordDeadRemoveWrites live [name])
              (WordAlloc.liveExpressionKeys address))
      | .store | .store8 | .store16 | .store32 =>
          (.shareInst operator name address,
            wordDeadAddReads live
              ([name] ++ WordAlloc.liveExpressionKeys address))
termination_by program => sizeOf program
decreasing_by
  all_goals simp_wf
  all_goals omega

def wordDeadCodeAux : WordProg α → List Nat → List (List Nat × List Nat) →
    WordProg α × List Nat
  | program, live, frames =>
      wordDeadCodeAuxWithLabels program live frames (wordDeadReturnLabels program)

def wordDeadCode : WordProg α → List Nat → WordProg α × List Nat
  | program, live => wordDeadCodeAuxWithLabels program live [] (wordDeadReturnLabels program)

/-! Cake's `remove_dead` carries a second backward set, `nlive`, for global
    stores (`word_allocScript.sml:938-1027`).  A direct `Set store (Var r)`
    can be removed when the same store is already in `nlive`, because the
    later write is the only observable value.  Ordinary memory stores and
    non-variable global expressions reset this information, as do control
    flow boundaries.  The old pair-valued helper above remains available for
    local proofs; production dead-program elimination uses this exact
    three-component state. -/

def wordDeadStoreKey [WordCseHash α] (store : WordStore α) : Nat :=
  wordCseStoreCode store

def wordDeadForgetStore [WordCseHash α] (store : WordStore α)
    (nlive : List Nat) : List Nat :=
  nlive.filter (fun key => key != wordDeadStoreKey store)

def wordDeadCodeWithStores [WordCseHash α] : WordProg α → List Nat →
    List (List Nat × List Nat) → List Nat → List Nat →
    WordProg α × List Nat × List Nat
  | .skip, live, _, _, nlive => (.skip, live, nlive)
  | .move priority moves, live, _, _, nlive =>
      let (program, live) := wordDeadMove priority live moves
      (program, live, nlive)
  | .assign destination value, live, _, _, nlive =>
      let (program, live) := wordDeadCodeAuxWithLabels
        (.assign destination value) live [] []
      (program, live, nlive)
  | .inst instruction, live, _, _, nlive =>
      let (program, live) := wordDeadInst live instruction
      (program, live, nlive)
  | .get destination store, live, _, _, nlive =>
      if destination ∈ live then
        (.get destination store,
          wordDeadAddReads (wordDeadRemoveWrites live [destination]) [],
          wordDeadForgetStore store nlive)
      else
        (.skip, live, nlive)
  | .store address value, live, _, _, nlive =>
      (.store address value,
        wordDeadAddReads live (WordAlloc.liveExpressionKeys address ++ [value]), nlive)
  | .set store value, live, _, _, nlive =>
      match value with
      | .var source =>
          if wordDeadStoreKey store ∈ nlive then
            (.skip, live, nlive)
          else
            (.set store value, wordDeadAddReads live
              (WordAlloc.liveExpressionKeys (.var source : WordExp α)),
              wordDeadStoreKey store :: nlive)
      | _ =>
          (.set store value, wordDeadAddReads live (WordAlloc.liveExpressionKeys value), [])
  | .seq first second, live, frames, returnLabels, nlive =>
      let (second', secondLive, secondNLive) := wordDeadCodeWithStores
        second live frames returnLabels nlive
      let (first', firstLive, firstNLive) := wordDeadCodeWithStores
        first secondLive frames returnLabels secondNLive
      let program := match first', second' with
        | .skip, program => program
        | program, .skip => program
        | _, _ => .seq first' second'
      (program, firstLive, firstNLive)
  | .ite operator condition right thenBranch elseBranch, live, frames,
      returnLabels, nlive =>
      let (then', thenLive, thenNLive) := wordDeadCodeWithStores
        thenBranch live frames returnLabels nlive
      let (else', elseLive, elseNLive) := wordDeadCodeWithStores
        elseBranch live frames returnLabels nlive
      let rightReads := match right with
        | .imm _ => []
        | .reg name => [name]
      let live := wordDeadAddReads (thenLive ++ elseLive) (condition :: rightReads)
      let nlive := thenNLive.filter (fun key => key ∈ elseNLive)
      let program := match then', else' with
        | .skip, .skip => .skip
        | _, _ => .ite operator condition right then' else'
      (program, live, nlive)
  | .loop liveIn body liveOut, _live, frames, returnLabels, _nlive =>
      let (body', _, _) := wordDeadCodeWithStores body liveIn
        ((liveIn, liveOut) :: frames) returnLabels []
      (.loop liveIn body' liveOut, liveIn, [])
  | .mustTerminate body, live, frames, returnLabels, nlive =>
      let (body', live, nlive) := wordDeadCodeWithStores body live frames
        returnLabels nlive
      (.mustTerminate body', live, nlive)
  | .break label, _live, frames, _, _nlive =>
      (.break label, (wordClashTreeFindLoopFrame label frames).map Prod.snd |>.getD [], [])
  | .continue label, _live, frames, _, _nlive =>
      (.continue label, (wordClashTreeFindLoopFrame label frames).map Prod.fst |>.getD [], [])
  | .raise exception, live, _, _returnLabels, _nlive =>
      (.raise exception, wordDeadAddReads live [exception], [])
  | .return label values, live, _, _, _nlive =>
      (.return label values, wordDeadAddReads (label :: live) values, [])
  | .tick, live, _, _, nlive => (.tick, live, nlive)
  | .locValue destination source, live, _, _, nlive =>
      if destination ∈ live then
        (.locValue destination source,
          wordDeadAddReads (wordDeadRemoveWrites live [destination]) [], nlive)
      else
        (.skip, live, nlive)
  | .call (some (destinations, cutsets, returnCode, returnLabel, entryLabel))
      target arguments handler, live, frames, returnLabels, nlive =>
      let (returnCode', _, _) := wordDeadCodeWithStores returnCode live frames
        returnLabels nlive
      let handler' := match handler with
        | none => none
        | some (exception, body, handlerLabel, handlerEntryLabel) =>
            some (exception,
              (wordDeadCodeWithStores body live frames [] nlive).1,
              handlerLabel, handlerEntryLabel)
      (.call (some (destinations, cutsets, returnCode', returnLabel, entryLabel))
          target arguments handler',
        wordDeadCallLive cutsets arguments, [])
  | .call returns target arguments handler, _live, _, _, _nlive =>
      (.call returns target arguments handler, wordDeadAddReads [] arguments, [])
  | .alloc destination cutsets, _live, _, _, _nlive =>
      (.alloc destination cutsets,
        wordDeadAddReads [destination] (cutsets.1 ++ cutsets.2), [])
  | .storeConsts source bitmap codeLength dataLength constants, live, _, _, nlive =>
      (.storeConsts source bitmap codeLength dataLength constants,
        wordDeadAddReads (wordDeadRemoveWrites live [source, bitmap])
          [codeLength, dataLength], nlive)
  | .opCurrHeap operator destination source, live, _, _, nlive =>
      if destination ∈ live then
        (.opCurrHeap operator destination source,
          wordDeadAddReads (wordDeadRemoveWrites live [destination]) [source],
          wordDeadForgetStore (.currHeap : WordStore α) nlive)
      else
        (.skip, live, nlive)
  | .install codeBuffer codeLength dataBuffer dataLength cutsets, _live, _, _, nlive =>
      (.install codeBuffer codeLength dataBuffer dataLength cutsets,
        wordDeadAddReads [codeBuffer, codeLength, dataBuffer, dataLength]
          (cutsets.1 ++ cutsets.2), nlive)
  | .codeBufferWrite address value, live, _, _, nlive =>
      (.codeBufferWrite address value, wordDeadAddReads live [address, value], nlive)
  | .dataBufferWrite address value, live, _, _, nlive =>
      (.dataBufferWrite address value, wordDeadAddReads live [address, value], nlive)
  | .ffi function configuration configurationLength array arrayLength liveSet, _live,
      _, _, nlive =>
      (.ffi function configuration configurationLength array arrayLength liveSet,
        wordDeadAddReads [configuration, configurationLength, array, arrayLength]
          (liveSet.1 ++ liveSet.2), nlive)
  | .shareInst operator name address, live, _, _, nlive =>
      match operator with
      | .load | .load8 | .load16 | .load32 =>
          (.shareInst operator name address,
            wordDeadAddReads (wordDeadRemoveWrites live [name])
              (WordAlloc.liveExpressionKeys address), nlive)
      | .store | .store8 | .store16 | .store32 =>
          (.shareInst operator name address,
            wordDeadAddReads live ([name] ++ WordAlloc.liveExpressionKeys address), nlive)
def wordRemoveDeadProgram [WordCseHash α] (program : WordProg α) : WordProg α :=
  (wordDeadCodeWithStores program [] [] (wordDeadReturnLabels program) []).1

/-! Cake's two-register arithmetic pass turns a selected binary operation into
    a destination/source move followed by an in-place operation.  The Word
    carrier keeps the selected arithmetic as an assignment, so preserve that
    move preference at the same post-copy boundary. -/
def wordThreeToTwoReg : WordProg α → WordProg α
  | .assign destination (.op operator [.var left, .const value]) =>
      .seq (.move 0 [(destination, left)])
        (.assign destination (.op operator [.var destination, .const value]))
  | .assign destination (.op operator [.var left, .var right]) =>
      .seq (.move 0 [(destination, left)])
        (.assign destination (.op operator [.var destination, .var right]))
  | .seq first second =>
      .seq (wordThreeToTwoReg first) (wordThreeToTwoReg second)
  | .ite operator condition right thenBranch elseBranch =>
      .ite operator condition right (wordThreeToTwoReg thenBranch)
        (wordThreeToTwoReg elseBranch)
  | .loop liveIn body liveOut =>
      .loop liveIn (wordThreeToTwoReg body) liveOut
  | .mustTerminate body => .mustTerminate (wordThreeToTwoReg body)
  | .call (some (destinations, cutsets, returnCode, returnLabel, entryLabel))
      target arguments none =>
      .call (some (destinations, cutsets,
        wordThreeToTwoReg returnCode, returnLabel, entryLabel))
        target arguments none
  | .call (some (destinations, cutsets, returnCode, returnLabel, entryLabel))
      target arguments (some (exception, body, handlerLabel, handlerEntryLabel)) =>
      .call (some (destinations, cutsets,
        wordThreeToTwoReg returnCode, returnLabel, entryLabel))
        target arguments
        (some (exception, wordThreeToTwoReg body,
          handlerLabel, handlerEntryLabel))
  | .call none target arguments none =>
      .call none target arguments none
  | .call none target arguments (some (exception, body, handlerLabel, handlerEntryLabel)) =>
      .call none target arguments
        (some (exception, wordThreeToTwoReg body,
          handlerLabel, handlerEntryLabel))
  | program => program
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

/-! The post-copy `word_unreach` boundary.  The public WordUnreach module
    depends on this file for its dead-code definitions, so keep this small
    local copy here to preserve the allocator pass order without introducing
    an import cycle. -/
def wordCopyUnreachMergeMoves (first second : List (Nat × Nat)) :
    List (Nat × Nat) :=
  let rewritten := second.map (fun move =>
    (move.1, (lookupNatInfo move.2 first).getD move.2))
  (rewritten ++ first).foldl (fun seen move =>
    if seen.any (fun prior => prior.1 == move.1) then seen
    else move :: seen) [] |>.reverse

def wordCopyUnreachSeq (first second : WordProg α) : WordProg α :=
  match first, second with
  | .skip, program => program
  | .raise _, _ => first
  | .return _ _, _ => first
  | .break _, _ => first
  | .continue _, _ => first
  | .call none _ _ _, _ => first
  | .move firstPriority firstMoves, .skip =>
      .move firstPriority firstMoves
  | .move firstPriority firstMoves, .move secondPriority secondMoves =>
      .move (max firstPriority secondPriority)
        (wordCopyUnreachMergeMoves firstMoves secondMoves)
  | .move firstPriority firstMoves,
      .seq (.move secondPriority secondMoves) rest =>
      let merged := .move (max firstPriority secondPriority)
        (wordCopyUnreachMergeMoves firstMoves secondMoves)
      match rest with
      | .skip => merged
      | _ => .seq merged rest
  | _, .skip => first
  | _, _ => .seq first second

/-! `Seq_assoc_right` first flattens every sequence, including sequences
    nested in call continuations.  Keeping the parts as a list makes that
    association explicit and lets `wordCopyUnreachSeq` merge adjacent moves
    after copy propagation, just as Cake's `dest_Seq_Move` does.  The
    accumulator preserves the same preorder without rebuilding the left
    prefix with `++` at every sequence node. -/
def wordCopyUnreachPartsAcc : WordProg α → List (WordProg α) → List (WordProg α)
  | .seq first second, suffix =>
      wordCopyUnreachPartsAcc first (wordCopyUnreachPartsAcc second suffix)
  | .ite operator condition right thenBranch elseBranch, suffix =>
      (.ite operator condition right
        (wordCopyUnreachPartsAcc thenBranch [] |>.foldr wordCopyUnreachSeq .skip)
        (wordCopyUnreachPartsAcc elseBranch [] |>.foldr wordCopyUnreachSeq .skip)) :: suffix
  | .loop liveIn body liveOut, suffix =>
      (.loop liveIn (wordCopyUnreachPartsAcc body [] |>.foldr wordCopyUnreachSeq .skip)
        liveOut) :: suffix
  | .mustTerminate body, suffix =>
      (.mustTerminate (wordCopyUnreachPartsAcc body [] |>.foldr wordCopyUnreachSeq .skip))
        :: suffix
  | .call (some (destinations, cutsets, returnCode, returnLabel, entryLabel))
      target arguments handler, suffix =>
      let handler' := match handler with
        | none => none
        | some (exception, body, handlerLabel, handlerEntryLabel) =>
            some (exception,
              wordCopyUnreachPartsAcc body [] |>.foldr wordCopyUnreachSeq .skip,
              handlerLabel, handlerEntryLabel)
      (.call (some (destinations, cutsets,
          wordCopyUnreachPartsAcc returnCode [] |>.foldr wordCopyUnreachSeq .skip,
          returnLabel, entryLabel)) target arguments handler') :: suffix
  | program, suffix => program :: suffix
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def wordCopyUnreachParts (program : WordProg α) : List (WordProg α) :=
  wordCopyUnreachPartsAcc program []

def wordRemoveUnreachableAfterCopy (program : WordProg α) : WordProg α :=
  wordCopyUnreachParts program |>.foldr wordCopyUnreachSeq .skip

end Flapjack.RiscV

namespace Flapjack.RiscV.CakeRegAlloc

open Flapjack
open Flapjack.RiscV

/-! The source-shaped allocator boundary: full SSA is performed first, then
Cake's dead-program pass feeds the clash tree and IRC allocator.

Ordinary load16/store16 instructions are unsupported by the reviewed allocator
routes. Reject them recursively at entry, before each liveness-based dead pass,
and before graph construction/colouring. Checks preserve every accepted tree;
failure returns `none`, with no deletion or opcode substitution. This checked
safety boundary does not prove universal source-to-boundary closure. -/
/-- Flapjack-only executed allocation result. Retain the real IRC colouring
so the native Word-to-Stack route can consume coloured Word names without
reconstructing them from locations. There is no separate HOL declaration
for this production-carrier packaging. -/
structure CakeAllocationWithColour (α : Type u) where
  ssaState : WordSsaState
  parameters : List Nat
  program : WordProg α
  allocation : WordSpillState
  colouring : NatInfoMap Nat

/-- Preserve the historical caller contract; its program remains SSA-shaped
and its spill-state locations carry the allocation. Flapjack-only projection. -/
def CakeAllocationWithColour.toLegacy (result : CakeAllocationWithColour α) :
    WordSsaState × List Nat × WordProg α × WordSpillState :=
  (result.ssaState, result.parameters, result.program, result.allocation)

/-- Materialize exactly the colouring used by the frame calculation.
This is a production-carrier operation, not a HOL compiler correctness claim. -/
def CakeAllocationWithColour.colouredProgram (result : CakeAllocationWithColour α) : WordProg α :=
  wordApplyColour (CakeAlloc.totalColour result.colouring) result.program

def cakeAllocateWordFunctionAfterDeadWithColour [OfNat α 0] [WordCseHash α] (currentFunction : Nat)
    (parameters : List Nat) (program : WordProg α) [BEq α] :
    Option (CakeAllocationWithColour α) :=
  if !allocatorMemorySupported program then none else
  let (state, renamedParameters, ssaProgram) :=
    wordFullSsaCcTrans parameters.length program
  if !allocatorMemorySupported ssaProgram then none else
  let ssaProgram := wordRemoveDeadProgram ssaProgram
  let ssaProgram := wordCseProp ssaProgram
  let ssaProgram := wordCopyProp ssaProgram
  let ssaProgram := wordThreeToTwoReg ssaProgram
  let ssaProgram := wordRemoveUnreachableAfterCopy ssaProgram
  if !allocatorMemorySupported ssaProgram then none else
  let ssaProgram := wordRemoveDeadProgram ssaProgram
  if !allocatorMemorySupported ssaProgram then none else
  let tree := wordClashTree ssaProgram []
  let fs := cakeGetStackOnly ssaProgram
  let forced := cakeGetForced ssaProgram
  let (wordMoves, spillCosts) := wordGetHeuristics 3 currentFunction ssaProgram
  let moves := wordMoves.map (fun move => (move.priority, (move.left, move.right)))
  let bij := cakeMkBij tree
  /- `word_alloc` passes this source-keyed sptree directly to `reg_alloc`.
     Keep those keys intact; `CakeNodeMap` stores keys outside the allocator
     array when necessary, matching `lookup_any` in `st_ex_list_MIN_cost`. -/
  let scost := spillCosts.map (cakeSpillCostMap bij.nextNode)
  let initialState := cakeInitRaStateFromBij bij tree forced fs
  match cakeDoRegAllocFromState .irc scost cakeRiscVRegisterCount
      moves bij initialState with
  | none => none
  | some colouring =>
      some ⟨state, renamedParameters, ssaProgram,
        cakeColourWordSpillState cakeRiscVRegisterCount
          parameters ssaProgram colouring, colouring⟩

/-- Historical executed API, now a projection of the shared result retaining
its actual colouring. Guard/pass order and allocation inputs are shared. -/
def cakeAllocateWordFunctionAfterDead [OfNat α 0] [WordCseHash α] (currentFunction : Nat)
    (parameters : List Nat) (program : WordProg α) [BEq α] :
    Option (WordSsaState × List Nat × WordProg α × WordSpillState) :=
  (cakeAllocateWordFunctionAfterDeadWithColour currentFunction parameters program).map
    CakeAllocationWithColour.toLegacy

/-- The retained colouring is precisely the one used to construct the actual
spill state, derived from the executed result equation. Flapjack-only carrier
infrastructure; this is not a HOL allocation or pass-correctness theorem. -/
theorem cakeAllocateWordFunctionAfterDeadWithColour_allocation
    {α : Type} [OfNat α 0] [WordCseHash α] [BEq α]
    (currentFunction : Nat) (parameters : List Nat) (program : WordProg α)
    (output : CakeAllocationWithColour α)
    (h : cakeAllocateWordFunctionAfterDeadWithColour currentFunction parameters program = some output) :
    output.allocation = cakeColourWordSpillState cakeRiscVRegisterCount
      parameters output.program output.colouring := by
  unfold cakeAllocateWordFunctionAfterDeadWithColour at h
  repeat' (split at h <;> simp_all)
  all_goals rcases h with ⟨_, _, _, rfl⟩
  all_goals rfl

/-- The executed frame occupancy is computed from the actual retained
colouring and its coloured program, with the original argument-area floor.
No desired maximum equality or reconstructed colouring is assumed. This
does not yet relate the separate production maximum to native maxVarHOL. -/
theorem cakeAllocateWordFunctionAfterDeadWithColour_frame
    {α : Type} [OfNat α 0] [WordCseHash α] [BEq α]
    (currentFunction : Nat) (parameters : List Nat) (program : WordProg α)
    (output : CakeAllocationWithColour α)
    (h : cakeAllocateWordFunctionAfterDeadWithColour currentFunction parameters program = some output) :
    output.allocation.nextSpill =
      max ((wordProgCakeMaxVar output.colouredProgram / 2 + 1) - cakeRiscVRegisterCount)
        (parameters.length - cakeRiscVRegisterCount) := by
  rw [cakeAllocateWordFunctionAfterDeadWithColour_allocation currentFunction parameters program output h]
  exact cakeColourWordSpillState_nextSpill_eq_occupancy cakeRiscVRegisterCount
    parameters output.program output.colouring

/-- The shared executed result retains a recursively checked source program.
This is a guard certificate, not a source-semantics correctness theorem. -/
theorem cakeAllocateWordFunctionAfterDeadWithColour_output_supported
    {α : Type} [OfNat α 0] [WordCseHash α] [BEq α]
    (currentFunction : Nat) (parameters : List Nat) (program : WordProg α)
    (output : CakeAllocationWithColour α)
    (h : cakeAllocateWordFunctionAfterDeadWithColour currentFunction parameters program = some output) :
    allocatorMemorySupported output.program = true := by
  unfold cakeAllocateWordFunctionAfterDeadWithColour at h
  repeat' (split at h <;> simp_all)
  all_goals rcases h with ⟨_, _, checked, rfl⟩
  all_goals exact checked

/-- A successful executed allocator call certifies its complete input tree.
This certificate covers arbitrary word payloads, including the executed
BitVec caller, without an extra supported-input premise. This is not a port of a HOL declaration. -/
theorem cakeAllocateWordFunctionAfterDead_input_supported
    {α : Type} [OfNat α 0] [WordCseHash α] [BEq α]
    (currentFunction : Nat) (parameters : List Nat) (program : WordProg α)
    (output : WordSsaState × List Nat × WordProg α × WordSpillState)
    (h : cakeAllocateWordFunctionAfterDead currentFunction parameters program = some output) :
    allocatorMemorySupported program = true := by
  unfold cakeAllocateWordFunctionAfterDead cakeAllocateWordFunctionAfterDeadWithColour at h
  split at h <;> simp_all [CakeAllocationWithColour.toLegacy]

/-- The program returned by successful allocation also passed the recursive
check immediately before clash-tree construction and colouring. -/
theorem cakeAllocateWordFunctionAfterDead_output_supported
    {α : Type} [OfNat α 0] [WordCseHash α] [BEq α]
    (currentFunction : Nat) (parameters : List Nat) (program : WordProg α)
    (output : WordSsaState × List Nat × WordProg α × WordSpillState)
    (h : cakeAllocateWordFunctionAfterDead currentFunction parameters program = some output) :
    allocatorMemorySupported output.2.2.1 = true := by
  unfold cakeAllocateWordFunctionAfterDead at h
  cases hc : cakeAllocateWordFunctionAfterDeadWithColour currentFunction parameters program with
  | none => simp [hc] at h
  | some shared =>
      simp only [hc, Option.map_some, Option.some.injEq] at h
      subst output
      exact cakeAllocateWordFunctionAfterDeadWithColour_output_supported
        currentFunction parameters program shared hc

/-- The successful API excludes unsupported input occurrences. -/
theorem cakeAllocateWordFunctionAfterDead_input_safe
    {α : Type} [OfNat α 0] [WordCseHash α] [BEq α]
    (currentFunction : Nat) (parameters : List Nat) (program : WordProg α)
    (output : WordSsaState × List Nat × WordProg α × WordSpillState)
    (h : cakeAllocateWordFunctionAfterDead currentFunction parameters program = some output) :
    ¬ UnsupportedAllocatorMemory program :=
  allocatorMemorySupported_excludes
    (cakeAllocateWordFunctionAfterDead_input_supported currentFunction parameters program output h)

end Flapjack.RiscV.CakeRegAlloc
