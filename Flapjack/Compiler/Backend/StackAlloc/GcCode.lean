import Flapjack.HolRef
import Flapjack.Compiler.Backend.StackLang.Overloads
import Flapjack.Compiler.Backend.StackRemove
import Flapjack.Compiler.Backend.BackendCommon
import Flapjack.Compiler.Backend.DataToWord.Config

/-!
# `stack_alloc` garbage-collector code

The stackLang implementations of the copying and generational collectors of
`cakeml/compiler/backend/stack_allocScript.sml:16-636` (`memcpy_code`,
`clear_top_inst`, the `word_gc_move*`/`word_gen_gc_move*`/
`word_gen_gc_partial_move*` `_code` definitions, `word_gc_partial_or_full`,
`SetNewTrigger` and `word_gc_code`), over the exact width-indexed
`HolProg width` carrier.  HOL `dimindex (:'a)` is `width`, `word_shift (:'a)`
and `shift (:'a)` are `wordShiftAmount width`, and the instruction overloads are
the tagged `stackLang` ports.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.StackRemove (leftShiftInst rightShiftInst constInst loadInst storeInst)

/-- Exact HOL `memcpy_code_def` (`stack_allocScript.sml:16-24`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml" "memcpy_code_def"
  (words_as_type_indexed_bitvec)]
def memcpyCode {width : Nat} [NeZero width] : HolProg width :=
  whileHOL .notEqual 0 (.imm 0)
    (listSeqHOL [loadInst 1 2, addBytesInWordInst 2, sub1Inst 0, storeInst 1 3,
      addBytesInWordInst 3])

/-- Exact HOL `clear_top_inst_def` (`stack_allocScript.sml:26-30`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml" "clear_top_inst_def"
  (words_as_type_indexed_bitvec)]
def clearTopInst {width : Nat} [NeZero width] (i n : Nat) : HolProg width :=
  .seq (leftShiftInst i (width - n - 1)) (rightShiftInst i (width - n - 1))

/-- Exact HOL `word_gc_move_code_def` (`stack_allocScript.sml:32-71`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml" "word_gc_move_code_def"
  (words_as_type_indexed_bitvec)]
def wordGcMoveCode {width : Nat} [NeZero width] (conf : Config) : HolProg width :=
  .ite .test 5 (.imm 1) .skip
    (listSeqHOL
      [moveHOL 0 5,
       .get 1 .currHeap,
       rightShiftInst 0 (shiftLength conf),
       leftShiftInst 0 (wordShiftAmount width),
       addInst 0 1,
       loadInst 1 0,
       .ite .test 1 (.imm 3)
         (listSeqHOL [rightShiftInst 1 2,
                      leftShiftInst 1 (shiftLength conf),
                      clearTopInst 5 (smallShiftLength conf - 1),
                      orInst 5 1])
         (listSeqHOL [rightShiftInst 1 (width - conf.lenSize),
                      add1Inst 1,
                      moveHOL 6 1,
                      moveHOL 2 0,
                      moveHOL 0 1,
                      memcpyCode,
                      moveHOL 0 6,
                      leftShiftInst 0 (wordShiftAmount width),
                      subInst 2 0,
                      moveHOL 0 4,
                      leftShiftInst 0 2,
                      storeInst 0 2,
                      moveHOL 1 4,
                      clearTopInst 5 (smallShiftLength conf - 1),
                      leftShiftInst 1 (shiftLength conf),
                      orInst 5 1,
                      addInst 4 6])])

/-- Exact HOL `word_gc_move_list_code_def` (`stack_allocScript.sml:73-81`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml" "word_gc_move_list_code_def"
  (words_as_type_indexed_bitvec)]
def wordGcMoveListCode {width : Nat} [NeZero width] (conf : Config) : HolProg width :=
  whileHOL .notEqual 7 (.imm 0)
    (listSeqHOL [loadInst 5 8, sub1Inst 7, wordGcMoveCode conf, storeInst 5 8,
      addBytesInWordInst 8])

/-- Exact HOL `word_gc_move_loop_code_def` (`stack_allocScript.sml:83-96`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml" "word_gc_move_loop_code_def"
  (words_as_type_indexed_bitvec)]
def wordGcMoveLoopCode {width : Nat} [NeZero width] (conf : Config) : HolProg width :=
  whileHOL .notEqual 3 (.reg 8)
    (listSeqHOL [loadInst 7 8,
      .ite .test 7 (.imm 4)
        (listSeqHOL [rightShiftInst 7 (width - conf.lenSize), addBytesInWordInst 8,
          wordGcMoveListCode conf])
        (listSeqHOL [rightShiftInst 7 (width - conf.lenSize), add1Inst 7,
          leftShiftInst 7 (wordShiftAmount width), addInst 8 7])])

/-- Exact HOL `word_gc_move_bitmap_code_def` (`stack_allocScript.sml:98-110`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml" "word_gc_move_bitmap_code_def"
  (words_as_type_indexed_bitvec)]
def wordGcMoveBitmapCode {width : Nat} [NeZero width] (conf : Config) : HolProg width :=
  whileHOL .notLower 7 (.imm 2)
    (.ite .test 7 (.imm 1)
      (listSeqHOL [rightShiftInst 7 1, addBytesInWordInst 8])
      (listSeqHOL [.stackLoadAny 5 8, rightShiftInst 7 1, wordGcMoveCode conf,
        .stackStoreAny 5 8, addBytesInWordInst 8]))

/-- Exact HOL `word_gc_move_bitmaps_code_def` (`stack_allocScript.sml:112-120`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml" "word_gc_move_bitmaps_code_def"
  (words_as_type_indexed_bitvec)]
def wordGcMoveBitmapsCode {width : Nat} [NeZero width] (conf : Config) : HolProg width :=
  whileHOL .notTest 0 (.reg 0)
    (listSeqHOL [.bitmapLoad 7 9, wordGcMoveBitmapCode conf, .bitmapLoad 0 9, add1Inst 9,
      rightShiftInst 0 (width - 1)])

/-- Exact HOL `word_gc_move_roots_bitmaps_code_def` (`stack_allocScript.sml:123-131`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml" "word_gc_move_roots_bitmaps_code_def"
  (words_as_type_indexed_bitvec)]
def wordGcMoveRootsBitmapsCode {width : Nat} [NeZero width] (conf : Config) :
    HolProg width :=
  whileHOL .notTest 9 (.reg 9)
    (listSeqHOL [moveHOL 0 9, sub1Inst 9, addBytesInWordInst 8, wordGcMoveBitmapsCode conf,
      .stackLoadAny 9 8])

/-- Exact HOL `word_gen_gc_move_code_def` (`stack_allocScript.sml:133-206`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml" "word_gen_gc_move_code_def"
  (words_as_type_indexed_bitvec)]
def wordGenGcMoveCode {width : Nat} [NeZero width] (conf : Config) : HolProg width :=
  .ite .test 5 (.imm 1) .skip
    (listSeqHOL
      [moveHOL 0 5,
       .get 1 .currHeap,
       rightShiftInst 0 (shiftLength conf),
       leftShiftInst 0 (wordShiftAmount width),
       addInst 0 1,
       loadInst 1 0,
       .ite .test 1 (.imm 3)
         (listSeqHOL [rightShiftInst 1 2,
                      leftShiftInst 1 (shiftLength conf),
                      clearTopInst 5 (smallShiftLength conf - 1),
                      orInst 5 1])
         (listSeqHOL [moveHOL 6 1,
                      rightShiftInst 1 (width - conf.lenSize),
                      add1Inst 1,
                      constInst 2 0b1100,
                      andInst 6 2,
                      .ite .equal 6 (.imm 8)
                        (listSeqHOL [
                          .set (.temp 0) 3,
                          .set (.temp 1) 4,
                          .get 3 (.temp 2),
                          .get 4 (.temp 3),
                          moveHOL 6 1,
                          leftShiftInst 1 (wordShiftAmount width),
                          subInst 4 6,
                          subInst 3 1,
                          .set (.temp 2) 3,
                          .set (.temp 3) 4,
                          moveHOL 2 0,
                          moveHOL 4 0,
                          moveHOL 0 6,
                          memcpyCode,
                          .get 0 (.temp 3),
                          leftShiftInst 0 2,
                          storeInst 0 4,
                          .get 1 (.temp 3),
                          clearTopInst 5 (smallShiftLength conf - 1),
                          leftShiftInst 1 (shiftLength conf),
                          orInst 5 1,
                          .get 3 (.temp 0),
                          .get 4 (.temp 1)])
                        (listSeqHOL [
                          moveHOL 6 1,
                          moveHOL 2 0,
                          moveHOL 0 1,
                          memcpyCode,
                          moveHOL 0 6,
                          leftShiftInst 0 (wordShiftAmount width),
                          subInst 2 0,
                          moveHOL 0 4,
                          leftShiftInst 0 2,
                          storeInst 0 2,
                          moveHOL 1 4,
                          clearTopInst 5 (smallShiftLength conf - 1),
                          leftShiftInst 1 (shiftLength conf),
                          orInst 5 1,
                          addInst 4 6])])])

/-- Exact HOL `word_gen_gc_partial_move_code_def` (`stack_allocScript.sml:208-255`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml" "word_gen_gc_partial_move_code_def"
  (words_as_type_indexed_bitvec)]
def wordGenGcPartialMoveCode {width : Nat} [NeZero width] (conf : Config) : HolProg width :=
  .ite .test 5 (.imm 1) .skip
    (listSeqHOL
      [moveHOL 0 5,
       .get 6 (.temp 0),
       rightShiftInst 0 (shiftLength conf),
       leftShiftInst 0 (wordShiftAmount width),
       .get 1 (.temp 1),
       .ite .lower 0 (.reg 6) .skip
        (.seq (.get 6 (.temp 1))
        (.ite .notLower 0 (.reg 1) .skip (listSeqHOL [
           .get 1 .currHeap,
           addInst 0 1,
           loadInst 1 0,
           .ite .test 1 (.imm 3)
             (listSeqHOL [rightShiftInst 1 2,
                          leftShiftInst 1 (shiftLength conf),
                          clearTopInst 5 (smallShiftLength conf - 1),
                          orInst 5 1])
             (listSeqHOL [moveHOL 6 1,
                          rightShiftInst 1 (width - conf.lenSize),
                          add1Inst 1,
                          moveHOL 6 1,
                          moveHOL 2 0,
                          moveHOL 0 1,
                          memcpyCode,
                          moveHOL 0 6,
                          leftShiftInst 0 (wordShiftAmount width),
                          subInst 2 0,
                          moveHOL 0 4,
                          leftShiftInst 0 2,
                          storeInst 0 2,
                          moveHOL 1 4,
                          clearTopInst 5 (smallShiftLength conf - 1),
                          leftShiftInst 1 (shiftLength conf),
                          orInst 5 1,
                          addInst 4 6])])))])

/-- Exact HOL `word_gen_gc_move_bitmap_code_def` (`stack_allocScript.sml:257-268`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml" "word_gen_gc_move_bitmap_code_def"
  (words_as_type_indexed_bitvec)]
def wordGenGcMoveBitmapCode {width : Nat} [NeZero width] (conf : Config) : HolProg width :=
  whileHOL .notLower 7 (.imm 2)
    (.ite .test 7 (.imm 1)
      (listSeqHOL [rightShiftInst 7 1, addBytesInWordInst 8])
      (listSeqHOL [.stackLoadAny 5 8, rightShiftInst 7 1, wordGenGcMoveCode conf,
        .stackStoreAny 5 8, addBytesInWordInst 8]))

/-- Exact HOL `word_gen_gc_partial_move_bitmap_code_def` (`stack_allocScript.sml:270-281`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml" "word_gen_gc_partial_move_bitmap_code_def"
  (words_as_type_indexed_bitvec)]
def wordGenGcPartialMoveBitmapCode {width : Nat} [NeZero width] (conf : Config) :
    HolProg width :=
  whileHOL .notLower 7 (.imm 2)
    (.ite .test 7 (.imm 1)
      (listSeqHOL [rightShiftInst 7 1, addBytesInWordInst 8])
      (listSeqHOL [.stackLoadAny 5 8, rightShiftInst 7 1, wordGenGcPartialMoveCode conf,
        .stackStoreAny 5 8, addBytesInWordInst 8]))

/-- Exact HOL `word_gen_gc_move_bitmaps_code_def` (`stack_allocScript.sml:284-292`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml" "word_gen_gc_move_bitmaps_code_def"
  (words_as_type_indexed_bitvec)]
def wordGenGcMoveBitmapsCode {width : Nat} [NeZero width] (conf : Config) : HolProg width :=
  whileHOL .notTest 0 (.reg 0)
    (listSeqHOL [.bitmapLoad 7 9, wordGenGcMoveBitmapCode conf, .bitmapLoad 0 9, add1Inst 9,
      rightShiftInst 0 (width - 1)])

/-- Exact HOL `word_gen_gc_partial_move_bitmaps_code_def` (`stack_allocScript.sml:295-303`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml"
  "word_gen_gc_partial_move_bitmaps_code_def" (words_as_type_indexed_bitvec)]
def wordGenGcPartialMoveBitmapsCode {width : Nat} [NeZero width] (conf : Config) :
    HolProg width :=
  whileHOL .notTest 0 (.reg 0)
    (listSeqHOL [.bitmapLoad 7 9, wordGenGcPartialMoveBitmapCode conf, .bitmapLoad 0 9,
      add1Inst 9, rightShiftInst 0 (width - 1)])

/-- Exact HOL `word_gen_gc_move_roots_bitmaps_code_def` (`stack_allocScript.sml:306-314`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml"
  "word_gen_gc_move_roots_bitmaps_code_def" (words_as_type_indexed_bitvec)]
def wordGenGcMoveRootsBitmapsCode {width : Nat} [NeZero width] (conf : Config) :
    HolProg width :=
  whileHOL .notTest 9 (.reg 9)
    (listSeqHOL [moveHOL 0 9, sub1Inst 9, addBytesInWordInst 8, wordGenGcMoveBitmapsCode conf,
      .stackLoadAny 9 8])

/-- Exact HOL `word_gen_gc_partial_move_roots_bitmaps_code_def`
(`stack_allocScript.sml:317-325`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml"
  "word_gen_gc_partial_move_roots_bitmaps_code_def" (words_as_type_indexed_bitvec)]
def wordGenGcPartialMoveRootsBitmapsCode {width : Nat} [NeZero width] (conf : Config) :
    HolProg width :=
  whileHOL .notTest 9 (.reg 9)
    (listSeqHOL [moveHOL 0 9, sub1Inst 9, addBytesInWordInst 8,
      wordGenGcPartialMoveBitmapsCode conf, .stackLoadAny 9 8])

/-- Exact HOL `word_gen_gc_move_list_code_def` (`stack_allocScript.sml:327-335`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml" "word_gen_gc_move_list_code_def"
  (words_as_type_indexed_bitvec)]
def wordGenGcMoveListCode {width : Nat} [NeZero width] (conf : Config) : HolProg width :=
  whileHOL .notEqual 7 (.imm 0)
    (listSeqHOL [loadInst 5 8, sub1Inst 7, wordGenGcMoveCode conf, storeInst 5 8,
      addBytesInWordInst 8])

/-- Exact HOL `word_gen_gc_partial_move_list_code_def` (`stack_allocScript.sml:337-345`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml"
  "word_gen_gc_partial_move_list_code_def" (words_as_type_indexed_bitvec)]
def wordGenGcPartialMoveListCode {width : Nat} [NeZero width] (conf : Config) :
    HolProg width :=
  whileHOL .notEqual 7 (.imm 0)
    (listSeqHOL [loadInst 5 8, sub1Inst 7, wordGenGcPartialMoveCode conf, storeInst 5 8,
      addBytesInWordInst 8])

/-- Exact HOL `word_gen_gc_move_data_code_def` (`stack_allocScript.sml:347-359`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml" "word_gen_gc_move_data_code_def"
  (words_as_type_indexed_bitvec)]
def wordGenGcMoveDataCode {width : Nat} [NeZero width] (conf : Config) : HolProg width :=
  whileHOL .notEqual 3 (.reg 8)
    (listSeqHOL [loadInst 7 8,
      .ite .test 7 (.imm 4)
        (listSeqHOL [rightShiftInst 7 (width - conf.lenSize), addBytesInWordInst 8,
          wordGenGcMoveListCode conf])
        (listSeqHOL [rightShiftInst 7 (width - conf.lenSize), add1Inst 7,
          leftShiftInst 7 (wordShiftAmount width), addInst 8 7])])

/-- Exact HOL `word_gen_gc_partial_move_ref_list_code_def` (`stack_allocScript.sml:361-368`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml"
  "word_gen_gc_partial_move_ref_list_code_def" (words_as_type_indexed_bitvec)]
def wordGenGcPartialMoveRefListCode {width : Nat} [NeZero width] (conf : Config) :
    HolProg width :=
  whileHOL .notEqual 9 (.reg 8)
    (listSeqHOL [loadInst 7 8, rightShiftInst 7 (width - conf.lenSize), addBytesInWordInst 8,
      wordGenGcPartialMoveListCode conf])

/-- Exact HOL `word_gen_gc_partial_move_data_code_def` (`stack_allocScript.sml:370-382`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml"
  "word_gen_gc_partial_move_data_code_def" (words_as_type_indexed_bitvec)]
def wordGenGcPartialMoveDataCode {width : Nat} [NeZero width] (conf : Config) :
    HolProg width :=
  whileHOL .notEqual 3 (.reg 8)
    (listSeqHOL [loadInst 7 8,
      .ite .test 7 (.imm 4)
        (listSeqHOL [rightShiftInst 7 (width - conf.lenSize), addBytesInWordInst 8,
          wordGenGcPartialMoveListCode conf])
        (listSeqHOL [rightShiftInst 7 (width - conf.lenSize), add1Inst 7,
          leftShiftInst 7 (wordShiftAmount width), addInst 8 7])])

/-- Exact HOL `word_gen_gc_move_refs_code_def` (`stack_allocScript.sml:384-393`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml" "word_gen_gc_move_refs_code_def"
  (words_as_type_indexed_bitvec)]
def wordGenGcMoveRefsCode {width : Nat} [NeZero width] (conf : Config) : HolProg width :=
  whileHOL .notEqual 0 (.reg 8)
    (listSeqHOL [loadInst 7 8, rightShiftInst 7 (width - conf.lenSize), addBytesInWordInst 8,
      wordGenGcMoveListCode conf, .get 0 (.temp 4)])

/-- Exact HOL `word_gen_gc_move_loop_code_def` (`stack_allocScript.sml:395-427`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml" "word_gen_gc_move_loop_code_def"
  (words_as_type_indexed_bitvec)]
def wordGenGcMoveLoopCode {width : Nat} [NeZero width] (conf : Config) : HolProg width :=
  whileHOL .notTest 7 (.reg 7)
    (.ite .equal 1 (.reg 2)
      (listSeqHOL [wordGenGcMoveDataCode conf, .get 5 (.temp 2), .get 7 (.temp 4), moveHOL 1 7,
        moveHOL 2 5, subInst 7 5])
      (listSeqHOL [moveHOL 0 1, .set (.temp 6) 8, moveHOL 8 2, .set (.temp 5) 8,
        wordGenGcMoveRefsCode conf, moveHOL 7 8, .get 1 (.temp 5), .get 2 (.temp 5),
        .set (.temp 4) 2, .get 2 (.temp 2), moveHOL 3 3, moveHOL 4 4, moveHOL 7 1,
        subInst 7 2, .get 8 (.temp 6), moveHOL 5 8, subInst 5 3, orInst 7 5]))

/-- Exact HOL `word_gc_partial_or_full_def` (`stack_allocScript.sml:429-440`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml" "word_gc_partial_or_full_def"
  (words_as_type_indexed_bitvec)]
def wordGcPartialOrFull {width : Nat} [NeZero width] (genSizes : List Nat)
    (partialCode fullCode : List (HolProg width)) : HolProg width :=
  match genSizes with
  | [] => listSeqHOL ([.get 8 .triggerGC, .get 7 .endOfHeap, subInst 7 8] ++ fullCode)
  | _ => listSeqHOL
      [.get 8 .triggerGC, .get 7 .endOfHeap, subInst 7 8,
       .ite .notLower 7 (.reg 1) (listSeqHOL partialCode) (listSeqHOL fullCode)]

/-- Exact HOL `SetNewTrigger_def` (`stack_allocScript.sml:442-457`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml" "SetNewTrigger_def"
  (words_as_type_indexed_bitvec)]
def setNewTrigger {width : Nat} [NeZero width] (endh ib : Nat) (gs : List Nat) :
    HolProg width :=
  listSeqHOL [constInst 1 (getGenSize gs : BitVec width),
    .get 7 .allocSize,
    moveHOL 4 endh,
    subInst 4 ib,
    .ite .lower 1 (.reg 7)
      (.ite .lower 4 (.reg 7)
        (.set .triggerGC endh)
        (.ite .test 7 (.imm (if width = 32 then 3 else 7))
          (.seq (addInst 7 ib) (.set .triggerGC 7))
          (.set .triggerGC endh)))
      (.ite .lower 4 (.reg 1)
        (.set .triggerGC endh)
        (.seq (addInst 1 ib) (.set .triggerGC 1)))]

/-- Exact HOL `word_gc_code_def` (`stack_allocScript.sml:459-636`): the `None`,
`Simple` and `Generational` (partial and full) collector stubs. -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml" "word_gc_code_def"
  (words_as_type_indexed_bitvec)]
def wordGcCode {width : Nat} [NeZero width] (conf : Config) : HolProg width :=
  match conf.gcKind with
  | .none =>
      listSeqHOL
        [.set .allocSize 1,
         .get 2 .currHeap,
         .set .nextFree 2,
         .set .triggerGC 2,
         .set .endOfHeap 2,
         .ite .test 1 (.reg 1) .skip (.seq (constInst 1 1) (.halt 1))]
  | .simple =>
      listSeqHOL
        [.set .allocSize 1,
         .set .nextFree 0,
         constInst 1 0,
         moveHOL 2 1,
         .get 3 .otherHeap,
         moveHOL 4 1,
         .get 5 .globals,
         moveHOL 6 1,
         moveHOL 8 1,
         wordGcMoveCode conf,
         .set .globals 5,
         moveHOL 7 5,
         rightShiftInst 7 (shiftLength conf),
         leftShiftInst 7 (wordShiftAmount width),
         .get 9 .otherHeap,
         addInst 7 9,
         .set .globReal 7,
         constInst 7 0,
         .stackLoadAny 9 8,
         moveHOL 8 7,
         wordGcMoveRootsBitmapsCode conf,
         .get 8 .otherHeap,
         wordGcMoveLoopCode conf,
         .get 0 .currHeap,
         .get 1 .otherHeap,
         .get 2 .heapLength,
         addInst 2 1,
         .set .currHeap 1,
         .set .otherHeap 0,
         .get 0 .nextFree,
         .set .nextFree 8,
         .set .endOfHeap 2,
         .set .triggerGC 2,
         .get 1 .allocSize,
         subInst 2 8,
         .ite .lower 2 (.reg 1) (.seq (constInst 1 1) (.halt 1)) .skip]
  | .generational genSizes =>
      wordGcPartialOrFull genSizes
        [.set .allocSize 1,
         .set .nextFree 0,
         .get 4 .genStart,
         .get 5 .endOfHeap,
         .get 2 .currHeap,
         .set (.temp 0) 4,
         subInst 5 2,
         .set (.temp 1) 5,
         .get 7 .heapLength,
         .get 5 .globals,
         .get 3 .otherHeap,
         rightShiftInst 4 (wordShiftAmount width),
         moveHOL 6 3,
         wordGenGcPartialMoveCode conf,
         .set .globals 5,
         moveHOL 8 5,
         rightShiftInst 8 (shiftLength conf),
         leftShiftInst 8 (wordShiftAmount width),
         .get 9 .currHeap,
         addInst 8 9,
         .set .globReal 8,
         constInst 8 0,
         .stackLoadAny 9 8,
         wordGenGcPartialMoveRootsBitmapsCode conf,
         .get 8 .currHeap,
         .get 9 .heapLength,
         addInst 9 8,
         .get 8 .endOfHeap,
         wordGenGcPartialMoveRefListCode conf,
         .get 8 .otherHeap,
         wordGenGcPartialMoveDataCode conf,
         .get 2 .otherHeap,
         moveHOL 0 3,
         subInst 0 2,
         rightShiftInst 0 (wordShiftAmount width),
         .get 3 .genStart,
         .get 1 .currHeap,
         addInst 3 1,
         memcpyCode,
         .get 0 .nextFree,
         .set .nextFree 3,
         .get 8 .endOfHeap,
         .get 2 .triggerGC,
         setNewTrigger 8 3 genSizes,
         constInst 1 0,
         .set (.temp 0) 1,
         .set (.temp 1) 1,
         .get 1 .allocSize,
         subInst 8 3,
         .get 7 .currHeap,
         subInst 3 7,
         .set .genStart 3]
        [.set .allocSize 1,
         .set .nextFree 0,
         constInst 1 0,
         moveHOL 2 1,
         .get 3 .otherHeap,
         .get 4 .heapLength,
         addInst 4 3,
         .set (.temp 0) 4,
         .set (.temp 1) 4,
         .set (.temp 2) 4,
         .set (.temp 4) 4,
         .set (.temp 5) 4,
         .set (.temp 6) 4,
         .get 4 .heapLength,
         rightShiftInst 4 (wordShiftAmount width),
         .set (.temp 3) 4,
         moveHOL 4 1,
         .get 5 .globals,
         moveHOL 6 1,
         moveHOL 8 1,
         wordGenGcMoveCode conf,
         .set .globals 5,
         moveHOL 7 5,
         .get 9 .otherHeap,
         rightShiftInst 7 (shiftLength conf),
         leftShiftInst 7 (wordShiftAmount width),
         addInst 7 9,
         .set .globReal 7,
         constInst 7 0,
         .stackLoadAny 9 8,
         moveHOL 8 7,
         wordGenGcMoveRootsBitmapsCode conf,
         .get 2 (.temp 2),
         .get 8 .otherHeap,
         moveHOL 7 3,
         subInst 7 8,
         .get 1 (.temp 6),
         moveHOL 6 2,
         subInst 6 1,
         orInst 7 6,
         wordGenGcMoveLoopCode conf,
         .get 0 .currHeap,
         .get 1 .otherHeap,
         .get 2 (.temp 2),
         .set .currHeap 1,
         .set .otherHeap 0,
         .get 0 .nextFree,
         .set .nextFree 3,
         .set .endOfHeap 2,
         moveHOL 8 3,
         subInst 8 1,
         .set .genStart 8,
         setNewTrigger 2 3 genSizes,
         constInst 1 0,
         .set (.temp 0) 1,
         .set (.temp 1) 1,
         .set (.temp 2) 1,
         .set (.temp 3) 1,
         .set (.temp 4) 1,
         .set (.temp 5) 1,
         .set (.temp 6) 1,
         .get 1 .allocSize,
         .get 2 .triggerGC,
         subInst 2 3,
         .ite .lower 2 (.reg 1) (.seq (constInst 1 1) (.halt 1)) .skip]

end Flapjack.Compiler.Backend.StackAlloc
