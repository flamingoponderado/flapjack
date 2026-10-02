import Flapjack.Compiler.Backend.WordToStack.Proofs.ReturnRegisterBounds

namespace Flapjack.Test.WordToStackReturnRegBoundParity
open Flapjack Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
/- Same-input whole register-bound observations from original HOL, including
violated bounds. These fixtures are regression evidence, not equivalence. -/

-- rrb_1_0_0_move_good
example : regBound (width := 1) (stackMoveNative 0 1180591620717411303425 3 1 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_1_0_0_move_bad
example : regBound (width := 1) (stackMoveNative 0 1180591620717411303425 3 2 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_1_0_0_aux
example : regBound (width := 1) (copyRetAuxNative 0 1180591620717411303425 0) 2 := by
  simp [ copyRetAuxNative, regBound]

-- rrb_1_0_0_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 1) false false (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_1_0_0_ret_0_0_1
example : regBound (copyRetNative (width := 1) false false (0,1180591620717411303425,true) ([] : List Nat) (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_1_0_0_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 1) false true (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_1_0_0_ret_0_1_1
example : regBound (copyRetNative (width := 1) false true (0,1180591620717411303425,true) ([] : List Nat) (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_1_0_0_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 1) true false (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_1_0_0_ret_1_0_1
example : regBound (copyRetNative (width := 1) true false (0,1180591620717411303425,true) ([] : List Nat) (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_1_0_0_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 1) true true (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_1_0_0_ret_1_1_1
example : regBound (copyRetNative (width := 1) true true (0,1180591620717411303425,true) ([] : List Nat) (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_1_0_4_move_good
example : regBound (width := 1) (stackMoveNative 0 1180591620717411303425 3 5 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_1_0_4_move_bad
example : regBound (width := 1) (stackMoveNative 0 1180591620717411303425 3 6 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_1_0_4_aux
example : regBound (width := 1) (copyRetAuxNative 4 1180591620717411303425 0) 6 := by
  simp [ copyRetAuxNative, regBound]

-- rrb_1_0_4_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 1) false false (4,1180591620717411303425,true) ([] : List Nat) (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_1_0_4_ret_0_0_1
example : regBound (copyRetNative (width := 1) false false (4,1180591620717411303425,true) ([] : List Nat) (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_1_0_4_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 1) false true (4,1180591620717411303425,true) ([] : List Nat) (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_1_0_4_ret_0_1_1
example : regBound (copyRetNative (width := 1) false true (4,1180591620717411303425,true) ([] : List Nat) (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_1_0_4_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 1) true false (4,1180591620717411303425,true) ([] : List Nat) (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_1_0_4_ret_1_0_1
example : regBound (copyRetNative (width := 1) true false (4,1180591620717411303425,true) ([] : List Nat) (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_1_0_4_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 1) true true (4,1180591620717411303425,true) ([] : List Nat) (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_1_0_4_ret_1_1_1
example : regBound (copyRetNative (width := 1) true true (4,1180591620717411303425,true) ([] : List Nat) (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_1_1_0_move_good
example : regBound (width := 1) (stackMoveNative 1 1180591620717411303425 3 1 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_1_1_0_move_bad
example : ¬ regBound (width := 1) (stackMoveNative 1 1180591620717411303425 3 2 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_1_1_0_aux
example : regBound (width := 1) (copyRetAuxNative 0 1180591620717411303425 1) 2 := by
  simp [ copyRetAuxNative, listSeq, regBound]

-- rrb_1_1_0_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 1) false false (0,1180591620717411303425,true) [2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_1_1_0_ret_0_0_1
example : regBound (copyRetNative (width := 1) false false (0,1180591620717411303425,true) [2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_1_1_0_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 1) false true (0,1180591620717411303425,true) [2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_1_1_0_ret_0_1_1
example : regBound (copyRetNative (width := 1) false true (0,1180591620717411303425,true) [2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_1_1_0_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 1) true false (0,1180591620717411303425,true) [2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_1_1_0_ret_1_0_1
example : regBound (copyRetNative (width := 1) true false (0,1180591620717411303425,true) [2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_1_1_0_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 1) true true (0,1180591620717411303425,true) [2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_1_1_0_ret_1_1_1
example : regBound (copyRetNative (width := 1) true true (0,1180591620717411303425,true) [2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_1_1_4_move_good
example : regBound (width := 1) (stackMoveNative 1 1180591620717411303425 3 5 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_1_1_4_move_bad
example : ¬ regBound (width := 1) (stackMoveNative 1 1180591620717411303425 3 6 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_1_1_4_aux
example : regBound (width := 1) (copyRetAuxNative 4 1180591620717411303425 1) 6 := by
  simp [ copyRetAuxNative, listSeq, regBound]

-- rrb_1_1_4_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 1) false false (4,1180591620717411303425,true) [2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_1_1_4_ret_0_0_1
example : regBound (copyRetNative (width := 1) false false (4,1180591620717411303425,true) [2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_1_1_4_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 1) false true (4,1180591620717411303425,true) [2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_1_1_4_ret_0_1_1
example : regBound (copyRetNative (width := 1) false true (4,1180591620717411303425,true) [2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_1_1_4_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 1) true false (4,1180591620717411303425,true) [2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_1_1_4_ret_1_0_1
example : regBound (copyRetNative (width := 1) true false (4,1180591620717411303425,true) [2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_1_1_4_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 1) true true (4,1180591620717411303425,true) [2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_1_1_4_ret_1_1_1
example : regBound (copyRetNative (width := 1) true true (4,1180591620717411303425,true) [2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_1_4_0_move_good
example : regBound (width := 1) (stackMoveNative 4 1180591620717411303425 3 1 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_1_4_0_move_bad
example : ¬ regBound (width := 1) (stackMoveNative 4 1180591620717411303425 3 2 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_1_4_0_aux
example : regBound (width := 1) (copyRetAuxNative 0 1180591620717411303425 4) 2 := by
  simp [ copyRetAuxNative, listSeq, regBound]

-- rrb_1_4_0_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 1) false false (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_1_4_0_ret_0_0_1
example : regBound (copyRetNative (width := 1) false false (0,1180591620717411303425,true) [2,2,2,2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_1_4_0_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 1) false true (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_1_4_0_ret_0_1_1
example : regBound (copyRetNative (width := 1) false true (0,1180591620717411303425,true) [2,2,2,2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_1_4_0_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 1) true false (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_1_4_0_ret_1_0_1
example : regBound (copyRetNative (width := 1) true false (0,1180591620717411303425,true) [2,2,2,2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_1_4_0_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 1) true true (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_1_4_0_ret_1_1_1
example : regBound (copyRetNative (width := 1) true true (0,1180591620717411303425,true) [2,2,2,2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_1_4_4_move_good
example : regBound (width := 1) (stackMoveNative 4 1180591620717411303425 3 5 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_1_4_4_move_bad
example : ¬ regBound (width := 1) (stackMoveNative 4 1180591620717411303425 3 6 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_1_4_4_aux
example : regBound (width := 1) (copyRetAuxNative 4 1180591620717411303425 4) 6 := by
  simp [ copyRetAuxNative, listSeq, regBound]

-- rrb_1_4_4_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 1) false false (4,1180591620717411303425,true) [2,2,2,2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_1_4_4_ret_0_0_1
example : regBound (copyRetNative (width := 1) false false (4,1180591620717411303425,true) [2,2,2,2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_1_4_4_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 1) false true (4,1180591620717411303425,true) [2,2,2,2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_1_4_4_ret_0_1_1
example : regBound (copyRetNative (width := 1) false true (4,1180591620717411303425,true) [2,2,2,2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_1_4_4_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 1) true false (4,1180591620717411303425,true) [2,2,2,2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_1_4_4_ret_1_0_1
example : regBound (copyRetNative (width := 1) true false (4,1180591620717411303425,true) [2,2,2,2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_1_4_4_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 1) true true (4,1180591620717411303425,true) [2,2,2,2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_1_4_4_ret_1_1_1
example : regBound (copyRetNative (width := 1) true true (4,1180591620717411303425,true) [2,2,2,2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_2_0_0_move_good
example : regBound (width := 2) (stackMoveNative 0 1180591620717411303425 3 1 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_2_0_0_move_bad
example : regBound (width := 2) (stackMoveNative 0 1180591620717411303425 3 2 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_2_0_0_aux
example : regBound (width := 2) (copyRetAuxNative 0 1180591620717411303425 0) 2 := by
  simp [ copyRetAuxNative, regBound]

-- rrb_2_0_0_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 2) false false (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_2_0_0_ret_0_0_1
example : regBound (copyRetNative (width := 2) false false (0,1180591620717411303425,true) ([] : List Nat) (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_2_0_0_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 2) false true (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_2_0_0_ret_0_1_1
example : regBound (copyRetNative (width := 2) false true (0,1180591620717411303425,true) ([] : List Nat) (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_2_0_0_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 2) true false (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_2_0_0_ret_1_0_1
example : regBound (copyRetNative (width := 2) true false (0,1180591620717411303425,true) ([] : List Nat) (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_2_0_0_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 2) true true (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_2_0_0_ret_1_1_1
example : regBound (copyRetNative (width := 2) true true (0,1180591620717411303425,true) ([] : List Nat) (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_2_0_4_move_good
example : regBound (width := 2) (stackMoveNative 0 1180591620717411303425 3 5 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_2_0_4_move_bad
example : regBound (width := 2) (stackMoveNative 0 1180591620717411303425 3 6 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_2_0_4_aux
example : regBound (width := 2) (copyRetAuxNative 4 1180591620717411303425 0) 6 := by
  simp [ copyRetAuxNative, regBound]

-- rrb_2_0_4_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 2) false false (4,1180591620717411303425,true) ([] : List Nat) (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_2_0_4_ret_0_0_1
example : regBound (copyRetNative (width := 2) false false (4,1180591620717411303425,true) ([] : List Nat) (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_2_0_4_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 2) false true (4,1180591620717411303425,true) ([] : List Nat) (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_2_0_4_ret_0_1_1
example : regBound (copyRetNative (width := 2) false true (4,1180591620717411303425,true) ([] : List Nat) (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_2_0_4_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 2) true false (4,1180591620717411303425,true) ([] : List Nat) (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_2_0_4_ret_1_0_1
example : regBound (copyRetNative (width := 2) true false (4,1180591620717411303425,true) ([] : List Nat) (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_2_0_4_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 2) true true (4,1180591620717411303425,true) ([] : List Nat) (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_2_0_4_ret_1_1_1
example : regBound (copyRetNative (width := 2) true true (4,1180591620717411303425,true) ([] : List Nat) (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_2_1_0_move_good
example : regBound (width := 2) (stackMoveNative 1 1180591620717411303425 3 1 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_2_1_0_move_bad
example : ¬ regBound (width := 2) (stackMoveNative 1 1180591620717411303425 3 2 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_2_1_0_aux
example : regBound (width := 2) (copyRetAuxNative 0 1180591620717411303425 1) 2 := by
  simp [ copyRetAuxNative, listSeq, regBound]

-- rrb_2_1_0_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 2) false false (0,1180591620717411303425,true) [2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_2_1_0_ret_0_0_1
example : regBound (copyRetNative (width := 2) false false (0,1180591620717411303425,true) [2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_2_1_0_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 2) false true (0,1180591620717411303425,true) [2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_2_1_0_ret_0_1_1
example : regBound (copyRetNative (width := 2) false true (0,1180591620717411303425,true) [2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_2_1_0_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 2) true false (0,1180591620717411303425,true) [2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_2_1_0_ret_1_0_1
example : regBound (copyRetNative (width := 2) true false (0,1180591620717411303425,true) [2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_2_1_0_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 2) true true (0,1180591620717411303425,true) [2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_2_1_0_ret_1_1_1
example : regBound (copyRetNative (width := 2) true true (0,1180591620717411303425,true) [2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_2_1_4_move_good
example : regBound (width := 2) (stackMoveNative 1 1180591620717411303425 3 5 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_2_1_4_move_bad
example : ¬ regBound (width := 2) (stackMoveNative 1 1180591620717411303425 3 6 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_2_1_4_aux
example : regBound (width := 2) (copyRetAuxNative 4 1180591620717411303425 1) 6 := by
  simp [ copyRetAuxNative, listSeq, regBound]

-- rrb_2_1_4_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 2) false false (4,1180591620717411303425,true) [2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_2_1_4_ret_0_0_1
example : regBound (copyRetNative (width := 2) false false (4,1180591620717411303425,true) [2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_2_1_4_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 2) false true (4,1180591620717411303425,true) [2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_2_1_4_ret_0_1_1
example : regBound (copyRetNative (width := 2) false true (4,1180591620717411303425,true) [2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_2_1_4_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 2) true false (4,1180591620717411303425,true) [2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_2_1_4_ret_1_0_1
example : regBound (copyRetNative (width := 2) true false (4,1180591620717411303425,true) [2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_2_1_4_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 2) true true (4,1180591620717411303425,true) [2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_2_1_4_ret_1_1_1
example : regBound (copyRetNative (width := 2) true true (4,1180591620717411303425,true) [2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_2_4_0_move_good
example : regBound (width := 2) (stackMoveNative 4 1180591620717411303425 3 1 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_2_4_0_move_bad
example : ¬ regBound (width := 2) (stackMoveNative 4 1180591620717411303425 3 2 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_2_4_0_aux
example : regBound (width := 2) (copyRetAuxNative 0 1180591620717411303425 4) 2 := by
  simp [ copyRetAuxNative, listSeq, regBound]

-- rrb_2_4_0_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 2) false false (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_2_4_0_ret_0_0_1
example : regBound (copyRetNative (width := 2) false false (0,1180591620717411303425,true) [2,2,2,2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_2_4_0_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 2) false true (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_2_4_0_ret_0_1_1
example : regBound (copyRetNative (width := 2) false true (0,1180591620717411303425,true) [2,2,2,2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_2_4_0_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 2) true false (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_2_4_0_ret_1_0_1
example : regBound (copyRetNative (width := 2) true false (0,1180591620717411303425,true) [2,2,2,2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_2_4_0_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 2) true true (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_2_4_0_ret_1_1_1
example : regBound (copyRetNative (width := 2) true true (0,1180591620717411303425,true) [2,2,2,2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_2_4_4_move_good
example : regBound (width := 2) (stackMoveNative 4 1180591620717411303425 3 5 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_2_4_4_move_bad
example : ¬ regBound (width := 2) (stackMoveNative 4 1180591620717411303425 3 6 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_2_4_4_aux
example : regBound (width := 2) (copyRetAuxNative 4 1180591620717411303425 4) 6 := by
  simp [ copyRetAuxNative, listSeq, regBound]

-- rrb_2_4_4_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 2) false false (4,1180591620717411303425,true) [2,2,2,2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_2_4_4_ret_0_0_1
example : regBound (copyRetNative (width := 2) false false (4,1180591620717411303425,true) [2,2,2,2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_2_4_4_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 2) false true (4,1180591620717411303425,true) [2,2,2,2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_2_4_4_ret_0_1_1
example : regBound (copyRetNative (width := 2) false true (4,1180591620717411303425,true) [2,2,2,2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_2_4_4_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 2) true false (4,1180591620717411303425,true) [2,2,2,2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_2_4_4_ret_1_0_1
example : regBound (copyRetNative (width := 2) true false (4,1180591620717411303425,true) [2,2,2,2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_2_4_4_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 2) true true (4,1180591620717411303425,true) [2,2,2,2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_2_4_4_ret_1_1_1
example : regBound (copyRetNative (width := 2) true true (4,1180591620717411303425,true) [2,2,2,2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_8_0_0_move_good
example : regBound (width := 8) (stackMoveNative 0 1180591620717411303425 3 1 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_8_0_0_move_bad
example : regBound (width := 8) (stackMoveNative 0 1180591620717411303425 3 2 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_8_0_0_aux
example : regBound (width := 8) (copyRetAuxNative 0 1180591620717411303425 0) 2 := by
  simp [ copyRetAuxNative, regBound]

-- rrb_8_0_0_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 8) false false (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_8_0_0_ret_0_0_1
example : regBound (copyRetNative (width := 8) false false (0,1180591620717411303425,true) ([] : List Nat) (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    regBound, copyRetAuxNative, listSeq]

-- rrb_8_0_0_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 8) false true (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_8_0_0_ret_0_1_1
example : regBound (copyRetNative (width := 8) false true (0,1180591620717411303425,true) ([] : List Nat) (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, regBound, copyRetAuxNative, listSeq]

-- rrb_8_0_0_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 8) true false (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_8_0_0_ret_1_0_1
example : regBound (copyRetNative (width := 8) true false (0,1180591620717411303425,true) ([] : List Nat) (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_8_0_0_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 8) true true (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_8_0_0_ret_1_1_1
example : regBound (copyRetNative (width := 8) true true (0,1180591620717411303425,true) ([] : List Nat) (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_8_0_4_move_good
example : regBound (width := 8) (stackMoveNative 0 1180591620717411303425 3 5 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_8_0_4_move_bad
example : regBound (width := 8) (stackMoveNative 0 1180591620717411303425 3 6 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_8_0_4_aux
example : regBound (width := 8) (copyRetAuxNative 4 1180591620717411303425 0) 6 := by
  simp [copyRetAuxNative, regBound]

-- rrb_8_0_4_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 8) false false (4,1180591620717411303425,true) ([] : List Nat) (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_8_0_4_ret_0_0_1
example : regBound (copyRetNative (width := 8) false false (4,1180591620717411303425,true) ([] : List Nat) (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_8_0_4_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 8) false true (4,1180591620717411303425,true) ([] : List Nat) (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_8_0_4_ret_0_1_1
example : regBound (copyRetNative (width := 8) false true (4,1180591620717411303425,true) ([] : List Nat) (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_8_0_4_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 8) true false (4,1180591620717411303425,true) ([] : List Nat) (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_8_0_4_ret_1_0_1
example : regBound (copyRetNative (width := 8) true false (4,1180591620717411303425,true) ([] : List Nat) (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_8_0_4_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 8) true true (4,1180591620717411303425,true) ([] : List Nat) (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_8_0_4_ret_1_1_1
example : regBound (copyRetNative (width := 8) true true (4,1180591620717411303425,true) ([] : List Nat) (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_8_1_0_move_good
example : regBound (width := 8) (stackMoveNative 1 1180591620717411303425 3 1 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_8_1_0_move_bad
example : ¬ regBound (width := 8) (stackMoveNative 1 1180591620717411303425 3 2 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_8_1_0_aux
example : regBound (width := 8) (copyRetAuxNative 0 1180591620717411303425 1) 2 := by
  simp [copyRetAuxNative, listSeq, regBound]

-- rrb_8_1_0_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 8) false false (0,1180591620717411303425,true) [2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_8_1_0_ret_0_0_1
example : regBound (copyRetNative (width := 8) false false (0,1180591620717411303425,true) [2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_8_1_0_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 8) false true (0,1180591620717411303425,true) [2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_8_1_0_ret_0_1_1
example : regBound (copyRetNative (width := 8) false true (0,1180591620717411303425,true) [2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_8_1_0_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 8) true false (0,1180591620717411303425,true) [2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_8_1_0_ret_1_0_1
example : regBound (copyRetNative (width := 8) true false (0,1180591620717411303425,true) [2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_8_1_0_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 8) true true (0,1180591620717411303425,true) [2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_8_1_0_ret_1_1_1
example : regBound (copyRetNative (width := 8) true true (0,1180591620717411303425,true) [2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_8_1_4_move_good
example : regBound (width := 8) (stackMoveNative 1 1180591620717411303425 3 5 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_8_1_4_move_bad
example : ¬ regBound (width := 8) (stackMoveNative 1 1180591620717411303425 3 6 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_8_1_4_aux
example : regBound (width := 8) (copyRetAuxNative 4 1180591620717411303425 1) 6 := by
  simp [copyRetAuxNative, listSeq, regBound]

-- rrb_8_1_4_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 8) false false (4,1180591620717411303425,true) [2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_8_1_4_ret_0_0_1
example : regBound (copyRetNative (width := 8) false false (4,1180591620717411303425,true) [2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_8_1_4_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 8) false true (4,1180591620717411303425,true) [2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_8_1_4_ret_0_1_1
example : regBound (copyRetNative (width := 8) false true (4,1180591620717411303425,true) [2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_8_1_4_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 8) true false (4,1180591620717411303425,true) [2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_8_1_4_ret_1_0_1
example : regBound (copyRetNative (width := 8) true false (4,1180591620717411303425,true) [2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_8_1_4_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 8) true true (4,1180591620717411303425,true) [2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_8_1_4_ret_1_1_1
example : regBound (copyRetNative (width := 8) true true (4,1180591620717411303425,true) [2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_8_4_0_move_good
example : regBound (width := 8) (stackMoveNative 4 1180591620717411303425 3 1 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_8_4_0_move_bad
example : ¬ regBound (width := 8) (stackMoveNative 4 1180591620717411303425 3 2 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_8_4_0_aux
example : regBound (width := 8) (copyRetAuxNative 0 1180591620717411303425 4) 2 := by
  simp [copyRetAuxNative, listSeq, regBound]

-- rrb_8_4_0_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 8) false false (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_8_4_0_ret_0_0_1
example : regBound (copyRetNative (width := 8) false false (0,1180591620717411303425,true) [2,2,2,2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_8_4_0_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 8) false true (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_8_4_0_ret_0_1_1
example : regBound (copyRetNative (width := 8) false true (0,1180591620717411303425,true) [2,2,2,2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_8_4_0_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 8) true false (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_8_4_0_ret_1_0_1
example : regBound (copyRetNative (width := 8) true false (0,1180591620717411303425,true) [2,2,2,2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_8_4_0_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 8) true true (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_8_4_0_ret_1_1_1
example : regBound (copyRetNative (width := 8) true true (0,1180591620717411303425,true) [2,2,2,2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_8_4_4_move_good
example : regBound (width := 8) (stackMoveNative 4 1180591620717411303425 3 5 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_8_4_4_move_bad
example : ¬ regBound (width := 8) (stackMoveNative 4 1180591620717411303425 3 6 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_8_4_4_aux
example : regBound (width := 8) (copyRetAuxNative 4 1180591620717411303425 4) 6 := by
  simp [copyRetAuxNative, listSeq, regBound]

-- rrb_8_4_4_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 8) false false (4,1180591620717411303425,true) [2,2,2,2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_8_4_4_ret_0_0_1
example : regBound (copyRetNative (width := 8) false false (4,1180591620717411303425,true) [2,2,2,2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_8_4_4_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 8) false true (4,1180591620717411303425,true) [2,2,2,2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_8_4_4_ret_0_1_1
example : regBound (copyRetNative (width := 8) false true (4,1180591620717411303425,true) [2,2,2,2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_8_4_4_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 8) true false (4,1180591620717411303425,true) [2,2,2,2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_8_4_4_ret_1_0_1
example : regBound (copyRetNative (width := 8) true false (4,1180591620717411303425,true) [2,2,2,2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_8_4_4_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 8) true true (4,1180591620717411303425,true) [2,2,2,2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_8_4_4_ret_1_1_1
example : regBound (copyRetNative (width := 8) true true (4,1180591620717411303425,true) [2,2,2,2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_64_0_0_move_good
example : regBound (width := 64) (stackMoveNative 0 1180591620717411303425 3 1 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_64_0_0_move_bad
example : regBound (width := 64) (stackMoveNative 0 1180591620717411303425 3 2 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_64_0_0_aux
example : regBound (width := 64) (copyRetAuxNative 0 1180591620717411303425 0) 2 := by
  simp [copyRetAuxNative, regBound]

-- rrb_64_0_0_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 64) false false (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_64_0_0_ret_0_0_1
example : regBound (copyRetNative (width := 64) false false (0,1180591620717411303425,true) ([] : List Nat) (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_64_0_0_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 64) false true (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_64_0_0_ret_0_1_1
example : regBound (copyRetNative (width := 64) false true (0,1180591620717411303425,true) ([] : List Nat) (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_64_0_0_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 64) true false (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_64_0_0_ret_1_0_1
example : regBound (copyRetNative (width := 64) true false (0,1180591620717411303425,true) ([] : List Nat) (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_64_0_0_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 64) true true (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_64_0_0_ret_1_1_1
example : regBound (copyRetNative (width := 64) true true (0,1180591620717411303425,true) ([] : List Nat) (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_64_0_4_move_good
example : regBound (width := 64) (stackMoveNative 0 1180591620717411303425 3 5 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_64_0_4_move_bad
example : regBound (width := 64) (stackMoveNative 0 1180591620717411303425 3 6 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_64_0_4_aux
example : regBound (width := 64) (copyRetAuxNative 4 1180591620717411303425 0) 6 := by
  simp [copyRetAuxNative, regBound]

-- rrb_64_0_4_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 64) false false (4,1180591620717411303425,true) ([] : List Nat) (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_64_0_4_ret_0_0_1
example : regBound (copyRetNative (width := 64) false false (4,1180591620717411303425,true) ([] : List Nat) (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_64_0_4_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 64) false true (4,1180591620717411303425,true) ([] : List Nat) (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_64_0_4_ret_0_1_1
example : regBound (copyRetNative (width := 64) false true (4,1180591620717411303425,true) ([] : List Nat) (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_64_0_4_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 64) true false (4,1180591620717411303425,true) ([] : List Nat) (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_64_0_4_ret_1_0_1
example : regBound (copyRetNative (width := 64) true false (4,1180591620717411303425,true) ([] : List Nat) (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_64_0_4_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 64) true true (4,1180591620717411303425,true) ([] : List Nat) (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_64_0_4_ret_1_1_1
example : regBound (copyRetNative (width := 64) true true (4,1180591620717411303425,true) ([] : List Nat) (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_64_1_0_move_good
example : regBound (width := 64) (stackMoveNative 1 1180591620717411303425 3 1 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_64_1_0_move_bad
example : ¬ regBound (width := 64) (stackMoveNative 1 1180591620717411303425 3 2 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_64_1_0_aux
example : regBound (width := 64) (copyRetAuxNative 0 1180591620717411303425 1) 2 := by
  simp [copyRetAuxNative, listSeq, regBound]

-- rrb_64_1_0_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 64) false false (0,1180591620717411303425,true) [2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_64_1_0_ret_0_0_1
example : regBound (copyRetNative (width := 64) false false (0,1180591620717411303425,true) [2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_64_1_0_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 64) false true (0,1180591620717411303425,true) [2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_64_1_0_ret_0_1_1
example : regBound (copyRetNative (width := 64) false true (0,1180591620717411303425,true) [2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_64_1_0_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 64) true false (0,1180591620717411303425,true) [2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_64_1_0_ret_1_0_1
example : regBound (copyRetNative (width := 64) true false (0,1180591620717411303425,true) [2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_64_1_0_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 64) true true (0,1180591620717411303425,true) [2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_64_1_0_ret_1_1_1
example : regBound (copyRetNative (width := 64) true true (0,1180591620717411303425,true) [2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_64_1_4_move_good
example : regBound (width := 64) (stackMoveNative 1 1180591620717411303425 3 5 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_64_1_4_move_bad
example : ¬ regBound (width := 64) (stackMoveNative 1 1180591620717411303425 3 6 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_64_1_4_aux
example : regBound (width := 64) (copyRetAuxNative 4 1180591620717411303425 1) 6 := by
  simp [copyRetAuxNative, listSeq, regBound]

-- rrb_64_1_4_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 64) false false (4,1180591620717411303425,true) [2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_64_1_4_ret_0_0_1
example : regBound (copyRetNative (width := 64) false false (4,1180591620717411303425,true) [2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_64_1_4_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 64) false true (4,1180591620717411303425,true) [2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_64_1_4_ret_0_1_1
example : regBound (copyRetNative (width := 64) false true (4,1180591620717411303425,true) [2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_64_1_4_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 64) true false (4,1180591620717411303425,true) [2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_64_1_4_ret_1_0_1
example : regBound (copyRetNative (width := 64) true false (4,1180591620717411303425,true) [2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_64_1_4_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 64) true true (4,1180591620717411303425,true) [2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_64_1_4_ret_1_1_1
example : regBound (copyRetNative (width := 64) true true (4,1180591620717411303425,true) [2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_64_4_0_move_good
example : regBound (width := 64) (stackMoveNative 4 1180591620717411303425 3 1 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_64_4_0_move_bad
example : ¬ regBound (width := 64) (stackMoveNative 4 1180591620717411303425 3 2 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_64_4_0_aux
example : regBound (width := 64) (copyRetAuxNative 0 1180591620717411303425 4) 2 := by
  simp [copyRetAuxNative, listSeq, regBound]

-- rrb_64_4_0_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 64) false false (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_64_4_0_ret_0_0_1
example : regBound (copyRetNative (width := 64) false false (0,1180591620717411303425,true) [2,2,2,2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_64_4_0_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 64) false true (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_64_4_0_ret_0_1_1
example : regBound (copyRetNative (width := 64) false true (0,1180591620717411303425,true) [2,2,2,2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_64_4_0_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 64) true false (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_64_4_0_ret_1_0_1
example : regBound (copyRetNative (width := 64) true false (0,1180591620717411303425,true) [2,2,2,2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_64_4_0_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 64) true true (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_64_4_0_ret_1_1_1
example : regBound (copyRetNative (width := 64) true true (0,1180591620717411303425,true) [2,2,2,2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_64_4_4_move_good
example : regBound (width := 64) (stackMoveNative 4 1180591620717411303425 3 5 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_64_4_4_move_bad
example : ¬ regBound (width := 64) (stackMoveNative 4 1180591620717411303425 3 6 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_64_4_4_aux
example : regBound (width := 64) (copyRetAuxNative 4 1180591620717411303425 4) 6 := by
  simp [copyRetAuxNative, listSeq, regBound]

-- rrb_64_4_4_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 64) false false (4,1180591620717411303425,true) [2,2,2,2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_64_4_4_ret_0_0_1
example : regBound (copyRetNative (width := 64) false false (4,1180591620717411303425,true) [2,2,2,2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_64_4_4_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 64) false true (4,1180591620717411303425,true) [2,2,2,2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_64_4_4_ret_0_1_1
example : regBound (copyRetNative (width := 64) false true (4,1180591620717411303425,true) [2,2,2,2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_64_4_4_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 64) true false (4,1180591620717411303425,true) [2,2,2,2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_64_4_4_ret_1_0_1
example : regBound (copyRetNative (width := 64) true false (4,1180591620717411303425,true) [2,2,2,2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_64_4_4_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 64) true true (4,1180591620717411303425,true) [2,2,2,2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_64_4_4_ret_1_1_1
example : regBound (copyRetNative (width := 64) true true (4,1180591620717411303425,true) [2,2,2,2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_80_0_0_move_good
example : regBound (width := 80) (stackMoveNative 0 1180591620717411303425 3 1 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_80_0_0_move_bad
example : regBound (width := 80) (stackMoveNative 0 1180591620717411303425 3 2 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_80_0_0_aux
example : regBound (width := 80) (copyRetAuxNative 0 1180591620717411303425 0) 2 := by
  simp [copyRetAuxNative, regBound]

-- rrb_80_0_0_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 80) false false (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_80_0_0_ret_0_0_1
example : regBound (copyRetNative (width := 80) false false (0,1180591620717411303425,true) ([] : List Nat) (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_80_0_0_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 80) false true (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_80_0_0_ret_0_1_1
example : regBound (copyRetNative (width := 80) false true (0,1180591620717411303425,true) ([] : List Nat) (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_80_0_0_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 80) true false (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_80_0_0_ret_1_0_1
example : regBound (copyRetNative (width := 80) true false (0,1180591620717411303425,true) ([] : List Nat) (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_80_0_0_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 80) true true (0,1180591620717411303425,true) ([] : List Nat) (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_80_0_0_ret_1_1_1
example : regBound (copyRetNative (width := 80) true true (0,1180591620717411303425,true) ([] : List Nat) (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_80_0_4_move_good
example : regBound (width := 80) (stackMoveNative 0 1180591620717411303425 3 5 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_80_0_4_move_bad
example : regBound (width := 80) (stackMoveNative 0 1180591620717411303425 3 6 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_80_0_4_aux
example : regBound (width := 80) (copyRetAuxNative 4 1180591620717411303425 0) 6 := by
  simp [copyRetAuxNative, regBound]

-- rrb_80_0_4_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 80) false false (4,1180591620717411303425,true) ([] : List Nat) (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_80_0_4_ret_0_0_1
example : regBound (copyRetNative (width := 80) false false (4,1180591620717411303425,true) ([] : List Nat) (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_80_0_4_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 80) false true (4,1180591620717411303425,true) ([] : List Nat) (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_80_0_4_ret_0_1_1
example : regBound (copyRetNative (width := 80) false true (4,1180591620717411303425,true) ([] : List Nat) (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_80_0_4_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 80) true false (4,1180591620717411303425,true) ([] : List Nat) (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_80_0_4_ret_1_0_1
example : regBound (copyRetNative (width := 80) true false (4,1180591620717411303425,true) ([] : List Nat) (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_80_0_4_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 80) true true (4,1180591620717411303425,true) ([] : List Nat) (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_80_0_4_ret_1_1_1
example : regBound (copyRetNative (width := 80) true true (4,1180591620717411303425,true) ([] : List Nat) (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_80_1_0_move_good
example : regBound (width := 80) (stackMoveNative 1 1180591620717411303425 3 1 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_80_1_0_move_bad
example : ¬ regBound (width := 80) (stackMoveNative 1 1180591620717411303425 3 2 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_80_1_0_aux
example : regBound (width := 80) (copyRetAuxNative 0 1180591620717411303425 1) 2 := by
  simp [copyRetAuxNative, listSeq, regBound]

-- rrb_80_1_0_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 80) false false (0,1180591620717411303425,true) [2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_80_1_0_ret_0_0_1
example : regBound (copyRetNative (width := 80) false false (0,1180591620717411303425,true) [2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_80_1_0_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 80) false true (0,1180591620717411303425,true) [2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_80_1_0_ret_0_1_1
example : regBound (copyRetNative (width := 80) false true (0,1180591620717411303425,true) [2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_80_1_0_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 80) true false (0,1180591620717411303425,true) [2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_80_1_0_ret_1_0_1
example : regBound (copyRetNative (width := 80) true false (0,1180591620717411303425,true) [2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_80_1_0_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 80) true true (0,1180591620717411303425,true) [2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_80_1_0_ret_1_1_1
example : regBound (copyRetNative (width := 80) true true (0,1180591620717411303425,true) [2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_80_1_4_move_good
example : regBound (width := 80) (stackMoveNative 1 1180591620717411303425 3 5 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_80_1_4_move_bad
example : ¬ regBound (width := 80) (stackMoveNative 1 1180591620717411303425 3 6 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_80_1_4_aux
example : regBound (width := 80) (copyRetAuxNative 4 1180591620717411303425 1) 6 := by
  simp [copyRetAuxNative, listSeq, regBound]

-- rrb_80_1_4_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 80) false false (4,1180591620717411303425,true) [2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_80_1_4_ret_0_0_1
example : regBound (copyRetNative (width := 80) false false (4,1180591620717411303425,true) [2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_80_1_4_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 80) false true (4,1180591620717411303425,true) [2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_80_1_4_ret_0_1_1
example : regBound (copyRetNative (width := 80) false true (4,1180591620717411303425,true) [2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_80_1_4_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 80) true false (4,1180591620717411303425,true) [2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_80_1_4_ret_1_0_1
example : regBound (copyRetNative (width := 80) true false (4,1180591620717411303425,true) [2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_80_1_4_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 80) true true (4,1180591620717411303425,true) [2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_80_1_4_ret_1_1_1
example : regBound (copyRetNative (width := 80) true true (4,1180591620717411303425,true) [2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet,
    regBound]

-- rrb_80_4_0_move_good
example : regBound (width := 80) (stackMoveNative 4 1180591620717411303425 3 1 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_80_4_0_move_bad
example : ¬ regBound (width := 80) (stackMoveNative 4 1180591620717411303425 3 2 (.halt 0)) 2 := by
  simp [stackMoveNative, regBound]

-- rrb_80_4_0_aux
example : regBound (width := 80) (copyRetAuxNative 0 1180591620717411303425 4) 2 := by
  simp [copyRetAuxNative, listSeq, regBound]

-- rrb_80_4_0_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 80) false false (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_80_4_0_ret_0_0_1
example : regBound (copyRetNative (width := 80) false false (0,1180591620717411303425,true) [2,2,2,2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_80_4_0_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 80) false true (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_80_4_0_ret_0_1_1
example : regBound (copyRetNative (width := 80) false true (0,1180591620717411303425,true) [2,2,2,2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_80_4_0_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 80) true false (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_80_4_0_ret_1_0_1
example : regBound (copyRetNative (width := 80) true false (0,1180591620717411303425,true) [2,2,2,2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_80_4_0_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 80) true true (0,1180591620717411303425,true) [2,2,2,2] (.halt 2)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_80_4_0_ret_1_1_1
example : regBound (copyRetNative (width := 80) true true (0,1180591620717411303425,true) [2,2,2,2] (.halt 0)) 2 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_80_4_4_move_good
example : regBound (width := 80) (stackMoveNative 4 1180591620717411303425 3 5 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_80_4_4_move_bad
example : ¬ regBound (width := 80) (stackMoveNative 4 1180591620717411303425 3 6 (.halt 4)) 6 := by
  simp [stackMoveNative, regBound]

-- rrb_80_4_4_aux
example : regBound (width := 80) (copyRetAuxNative 4 1180591620717411303425 4) 6 := by
  simp [copyRetAuxNative, listSeq, regBound]

-- rrb_80_4_4_ret_0_0_0
example : ¬ regBound (copyRetNative (width := 80) false false (4,1180591620717411303425,true) [2,2,2,2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_80_4_4_ret_0_0_1
example : regBound (copyRetNative (width := 80) false false (4,1180591620717411303425,true) [2,2,2,2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_80_4_4_ret_0_1_0
example : ¬ regBound (copyRetNative (width := 80) false true (4,1180591620717411303425,true) [2,2,2,2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_80_4_4_ret_0_1_1
example : regBound (copyRetNative (width := 80) false true (4,1180591620717411303425,true) [2,2,2,2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_80_4_4_ret_1_0_0
example : ¬ regBound (copyRetNative (width := 80) true false (4,1180591620717411303425,true) [2,2,2,2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_80_4_4_ret_1_0_1
example : regBound (copyRetNative (width := 80) true false (4,1180591620717411303425,true) [2,2,2,2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    listSeq, regBound]

-- rrb_80_4_4_ret_1_1_0
example : ¬ regBound (copyRetNative (width := 80) true true (4,1180591620717411303425,true) [2,2,2,2] (.halt 6)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

-- rrb_80_4_4_ret_1_1_1
example : regBound (copyRetNative (width := 80) true true (4,1180591620717411303425,true) [2,2,2,2] (.halt 4)) 6 := by
  simp [copyRetNative, Flapjack.Compiler.Backend.WordToStack.numStackRet, copyRetAuxNative, seqStackFreeNative,
    Flapjack.Compiler.Backend.WordToStack.handlerSlots, listSeq, regBound]

#print axioms Flapjack.WordToStackProofs.stackMoveRegBound
#print axioms Flapjack.WordToStackProofs.copyRetAuxRegBound
#print axioms Flapjack.WordToStackProofs.copyRetRegBound
end Flapjack.Test.WordToStackReturnRegBoundParity
