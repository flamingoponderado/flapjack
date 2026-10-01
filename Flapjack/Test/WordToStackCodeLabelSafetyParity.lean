import Flapjack.Compiler.Backend.WordToStack.Proofs.CodeLabelSafety

namespace Flapjack.Test.WordToStackCodeLabelSafetyParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm

private def snapshot {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (registers : Nat) (rows : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (external : Set Nat) : Prop × Prop :=
  let result := compileWordToStackNative c false registers rows (.append (.list [8]) (.list [2]),5)
  (goodCodeLabelsHOL rows external, stackGoodCodeLabels result.1 external)

macro "code_safety_replay" : tactic => `(tactic|
  (dsimp only [snapshot]
   simp only [goodCodeLabelsHOL, stackGoodCodeLabels, compileWordToStackNative, compileProgNative, List.map_cons, List.map_nil,
     List.mem_cons, List.mem_nil_iff, or_false, Set.ofPred_or, Set.ofPred_eq_eq_singleton,
     Set.ofPred_false, Set.image_union, Set.image_singleton, Set.image_empty,
     Set.sUnion_union, Set.sUnion_singleton, Set.sUnion_empty]
   apply Prod.ext
   all_goals first
     | (simp +decide [compileWordToStackNative, compileProgNative, maxVarHOL, compNative, getCodeLabels, getCodeLabelsHOL,
         stackGetHandlerLabels, goodHandlersHOL, wRegWrite1Native, wRegWrite2Native,
         wStackLoadNative, WordToStackRegFormat.wReg1, WordToStackRegFormat.wReg2,
         callDestNative, seqStackFreeNative, wLiveNative, stackArgsNative,
         stackHandlerArgsNative, stackMoveNative, copyRetNative, copyRetAuxNative,
         popHandlerNative, pushHandlerNative, listSeq, WordToStack.stackArgCount,
         WordToStack.numStackRet, WordToStack.skipFree, WordToStack.stackFree,
         WordToStack.insertBitmap,  Set.subset_def, or_assoc, or_left_comm, or_comm])
     | simp +decide [compileWordToStackNative, compileProgNative, maxVarHOL, compNative, goodHandlersHOL, wLiveNative, WordToStack.insertBitmap, WordToStack.constWordsToBitmapW, WordToStack.chunkToBitmapW, WordToStack.writeBitmapExact, WordToStack.wordListW, sptToAList, sptFoldi]
   all_goals first | decide | (simp +decide [Set.subset_def])))

-- cls_empty
example (c : AsmConfigExact 64) : snapshot c 4 [] {raiseStubLocation,storeConstsStubLocation} = (True,True) := by
  code_safety_replay

-- cls_self
example (c : AsmConfigExact 64) : snapshot c 4 [(7,0,.locValue 0 7)] {raiseStubLocation,storeConstsStubLocation} = (True,True) := by
  code_safety_replay

-- cls_missing
example (c : AsmConfigExact 64) : snapshot c 4 [(7,0,.locValue 0 8)] {raiseStubLocation,storeConstsStubLocation} = (False,False) := by
  code_safety_replay

-- cls_external
example (c : AsmConfigExact 64) : snapshot c 4 [(7,0,.locValue 99 8)] {raiseStubLocation,storeConstsStubLocation,8} = (True,True) := by
  code_safety_replay

-- cls_duplicates
example (c : AsmConfigExact 64) : snapshot c 4 [(7,0,.locValue 0 7),(7,99,.locValue 99 7)] {raiseStubLocation,storeConstsStubLocation} = (True,True) := by
  code_safety_replay

-- cls_owned
example (c : AsmConfigExact 64) : snapshot c 4 [(7,0,.call (some ([],(.ln,.ln),.locValue 0 8,11,12)) (some 10) [] (some (0,.locValue 0 9,7,5)))] {raiseStubLocation,storeConstsStubLocation,8,9,10} = (True,True) := by
  code_safety_replay

-- cls_wrong_owner
example (c : AsmConfigExact 64) : snapshot c 4 [(7,0,.call (some ([],(.ln,.ln),.locValue 0 8,11,12)) (some 10) [] (some (0,.locValue 0 9,9,5)))] {raiseStubLocation,storeConstsStubLocation,8,9,10} = (False,False) := by
  code_safety_replay

-- cls_tail_missing
example (c : AsmConfigExact 64) : snapshot c 4 [(7,0,.call none (some 7) [] (some (0,.locValue 0 8,999,5)))] {raiseStubLocation,storeConstsStubLocation} = (False,True) := by
  code_safety_replay

-- cls_threaded
example (c : AsmConfigExact 64) : snapshot c 4 [(7,5,.alloc 0 (.ln,.ln)),(8,0,.storeConsts 0 0 0 0 [])] {raiseStubLocation,storeConstsStubLocation} = (True,True) := by
  code_safety_replay

-- cls_width_one
example (c : AsmConfigExact 1) : snapshot c 0 [(7,0,.locValue 99 8)] Set.univ = (True,True) := by
  code_safety_replay

-- An actual full theorem application with arbitrary width/configuration,
-- register count and bitmap input; the compiler output is constructed, not assumed.
example {width : Nat} [NeZero width] (c : AsmConfigExact width) (registers : Nat)
    (bs : AppList (BitVec width) × Nat) :
    stackGoodCodeLabels
      (compileWordToStackNative c false registers [(7,0,.locValue 99 8)] bs).1 Set.univ := by
  apply wordToStackGoodCodeLabelsIncr c registers [(7,0,.locValue 99 8)] bs _
    (compileWordToStackNative c false registers [(7,0,.locValue 99 8)] bs).2.1
    (compileWordToStackNative c false registers [(7,0,.locValue 99 8)] bs).2.2 Set.univ
  · exact ⟨Set.mem_univ _,Set.mem_univ _,rfl⟩
  · constructor
    · rfl
    · simp only [Set.union_univ]
      exact Set.subset_univ _

-- Finite or infinite arbitrary external sets: derive the actual output safety
-- from concrete input memberships, without supplying a target predicate.
example {width : Nat} [NeZero width] (c : AsmConfigExact width) (registers : Nat)
    (bs : AppList (BitVec width) × Nat) (external : Set Nat)
    (raiseMember : raiseStubLocation ∈ external)
    (storeMember : storeConstsStubLocation ∈ external) (referenceMember : 8 ∈ external) :
    stackGoodCodeLabels
      (compileWordToStackNative c false registers [(7,0,.locValue 99 8)] bs).1 external := by
  apply wordToStackGoodCodeLabelsIncr c registers [(7,0,.locValue 99 8)] bs _
    (compileWordToStackNative c false registers [(7,0,.locValue 99 8)] bs).2.1
    (compileWordToStackNative c false registers [(7,0,.locValue 99 8)] bs).2.2 external
  · exact ⟨raiseMember,storeMember,rfl⟩
  · simp [goodCodeLabelsHOL,goodHandlersHOL,getCodeLabelsHOL,referenceMember]

end Flapjack.Test.WordToStackCodeLabelSafetyParity
