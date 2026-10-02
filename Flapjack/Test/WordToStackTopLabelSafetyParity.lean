import Flapjack.Compiler.Backend.WordToStack.Proofs.TopLabelSafety

set_option maxHeartbeats 1600000

namespace Flapjack.Test.WordToStackTopLabelSafetyParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm

private def snapshot {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (rows : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (external : Set Nat) : Prop × Prop × Prop :=
  let result := compileNative { c with regCount := 9, avoidRegs := [] } false rows
  (goodCodeLabelsHOL rows external, stackGoodCodeLabels result.2.2.2 external, stackGoodHandlerLabels result.2.2.2)

macro "top_safety_replay" : tactic => `(tactic|
  (simp +decide [snapshot, compileNative, goodCodeLabelsHOL, stackGoodCodeLabels,
    stackGoodHandlerLabels, raiseStubNative, storeConstsStubNative, BackendProps.restrictNonzero, compileWordToStackNative, compileProgNative, maxVarHOL, compNative, getCodeLabels, getCodeLabelsHOL,
         stackGetHandlerLabels, goodHandlersHOL, wRegWrite1Native, wRegWrite2Native,
         wStackLoadNative, WordToStackRegFormat.wReg1, WordToStackRegFormat.wReg2,
         callDestNative, seqStackFreeNative, wLiveNative, stackArgsNative,
         stackHandlerArgsNative, stackMoveNative, copyRetNative, copyRetAuxNative,
         popHandlerNative, pushHandlerNative, listSeq, WordToStack.stackArgCount,
         WordToStack.numStackRet, WordToStack.skipFree, WordToStack.stackFree,
         WordToStack.insertBitmap,  Set.subset_def, or_assoc, or_left_comm, or_comm, raiseStubLocation, storeConstsStubLocation,
    WordToStack.constWordsToBitmapW, WordToStack.chunkToBitmapW, WordToStack.writeBitmapExact,
    WordToStack.wordListW, sptToAList, sptFoldi]
   all_goals first | decide | (simp +decide [Set.subset_def])))

-- cls_empty
example (c : AsmConfigExact 64) : snapshot c [] ∅ = (True,True,True) := by
  top_safety_replay

-- cls_self
example (c : AsmConfigExact 64) : snapshot c [(7,0,.locValue 0 7)] ∅ = (True,True,True) := by
  top_safety_replay

-- cls_missing
example (c : AsmConfigExact 64) : snapshot c [(7,0,.locValue 0 8)] ∅ = (False,False,True) := by
  top_safety_replay

-- cls_external
example (c : AsmConfigExact 64) : snapshot c [(7,0,.locValue 99 8)] {8} = (True,True,True) := by
  top_safety_replay

-- cls_duplicates
example (c : AsmConfigExact 64) : snapshot c [(7,0,.locValue 0 7),(7,99,.locValue 99 7)] ∅ = (True,True,True) := by
  top_safety_replay

-- cls_owned
example (c : AsmConfigExact 64) : snapshot c [(7,0,.call (some ([],(.ln,.ln),.locValue 0 8,11,12)) (some 10) [] (some (0,.locValue 0 9,7,5)))] {8,9,10} = (True,True,True) := by
  top_safety_replay

-- cls_wrong_owner
example (c : AsmConfigExact 64) : snapshot c [(7,0,.call (some ([],(.ln,.ln),.locValue 0 8,11,12)) (some 10) [] (some (0,.locValue 0 9,9,5)))] {8,9,10} = (False,False,False) := by
  top_safety_replay

-- cls_tail_missing
example (c : AsmConfigExact 64) : snapshot c [(7,0,.call none (some 7) [] (some (0,.locValue 0 8,999,5)))] ∅ = (False,True,True) := by
  top_safety_replay

-- cls_threaded
example (c : AsmConfigExact 64) : snapshot c [(7,5,.alloc 0 (.ln,.ln)),(8,0,.storeConsts 0 0 0 0 [])] ∅ = (True,True,True) := by
  top_safety_replay

-- cls_width_one
example (c : AsmConfigExact 1) : snapshot c [(7,0,.locValue 99 8)] Set.univ = (True,True,True) := by
  top_safety_replay

-- top_raise_owned
example (c : AsmConfigExact 64) : snapshot c [(7,0,.locValue 0 raiseStubLocation)] ∅ = (False,True,True) := by
  top_safety_replay

-- top_store_owned
example (c : AsmConfigExact 64) : snapshot c [(7,0,.locValue 0 storeConstsStubLocation)] ∅ = (False,True,True) := by
  top_safety_replay

-- Full theorem applications to constructed output, arbitrary configuration,
-- positive width and external set. No stub membership is needed.
example {width : Nat} [NeZero width] (c : AsmConfigExact width) (external : Set Nat)
    (member : 8 ∈ external) :
    stackGoodCodeLabels (compileNative c false [(7,0,.locValue 99 8)]).2.2.2 external := by
  let result := compileNative c false [(7,0,.locValue 99 8)]
  apply wordToStackGoodCodeLabels c [(7,0,.locValue 99 8)] result.1 result.2.1
    result.2.2.1 result.2.2.2 external rfl
  simp [goodCodeLabelsHOL,goodHandlersHOL,getCodeLabelsHOL,member]

-- Handler safety needs no code-label guard, even for a missing code reference.
example {width : Nat} [NeZero width] (c : AsmConfigExact width) :
    stackGoodHandlerLabels (compileNative c false [(7,0,.locValue 99 8)]).2.2.2 := by
  let result := compileNative c false [(7,0,.locValue 99 8)]
  apply wordToStackGoodHandlerLabels c [(7,0,.locValue 99 8)] result.1 result.2.1
    result.2.2.1 result.2.2.2 rfl rfl

end Flapjack.Test.WordToStackTopLabelSafetyParity
