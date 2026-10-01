import Flapjack.Compiler.Backend.WordToStack.Proofs.ProgramCodeLabels

/-! Same-input original whole-program observations; kernel regression evidence,
not a HOL-to-Lean equivalence proof. -/
namespace Flapjack.Test.WordToStackProgramCodeLabelsParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm

private def snapshot (c : AsmConfigExact 64)
    (rows : List (Nat × Nat × WordLangProgHOL (BitVec 64))) :
    Set (Nat × Nat) × Set Nat × Set (Nat × Nat) × List Nat × Nat × Bool :=
  let result := compileWordToStackNative c false 4 rows (.append (.list [8]) (.list [2]),5)
  (Set.sUnion (getCodeLabels '' {p | p ∈ result.1.map Prod.snd}),
   Set.sUnion {labels | labels ∈ rows.map (fun row => getCodeLabelsHOL row.2.2)},
   Set.sUnion {labels | labels ∈ result.1.map (fun row => stackGetHandlerLabels row.1 row.2)},
   result.2.1, result.2.2.2, rows.all (fun row => goodHandlersHOL row.1 row.2.2))

macro "program_labels_replay" : tactic => `(tactic|
  (dsimp only [snapshot]
   simp only [compileWordToStackNative, compileProgNative, List.map_cons, List.map_nil,
     List.mem_cons, List.mem_nil_iff, or_false, Set.ofPred_or, Set.ofPred_eq_eq_singleton,
     Set.ofPred_false, Set.image_union, Set.image_singleton, Set.image_empty,
     Set.sUnion_union, Set.sUnion_singleton, Set.sUnion_empty]
   repeat' apply Prod.ext
   all_goals first
     | (ext label; simp +decide [compileWordToStackNative, compileProgNative, maxVarHOL, compNative, getCodeLabels, getCodeLabelsHOL,
         stackGetHandlerLabels, goodHandlersHOL, wRegWrite1Native, wRegWrite2Native,
         wStackLoadNative, WordToStackRegFormat.wReg1, WordToStackRegFormat.wReg2,
         callDestNative, seqStackFreeNative, wLiveNative, stackArgsNative,
         stackHandlerArgsNative, stackMoveNative, copyRetNative, copyRetAuxNative,
         popHandlerNative, pushHandlerNative, listSeq, WordToStack.stackArgCount,
         WordToStack.numStackRet, WordToStack.skipFree, WordToStack.stackFree,
         WordToStack.insertBitmap,  or_assoc, or_left_comm, or_comm])
     | simp +decide [compileWordToStackNative, compileProgNative, maxVarHOL, compNative, goodHandlersHOL, wLiveNative, WordToStack.insertBitmap, WordToStack.constWordsToBitmapW, WordToStack.chunkToBitmapW, WordToStack.writeBitmapExact, WordToStack.wordListW, sptToAList, sptFoldi]
   all_goals decide))

-- pl_empty
example (c : AsmConfigExact 64) :
    snapshot c [] = (∅,∅,∅,[],5,true) := by
  program_labels_replay

-- pl_duplicates
example (c : AsmConfigExact 64) :
    snapshot c [(7,0,.locValue 0 8),(7,0,.locValue 0 9)] = ({(8,0),(9,0)},{8,9},∅,[0,0],5,true) := by
  program_labels_replay

-- pl_spilled
example (c : AsmConfigExact 64) :
    snapshot c [(7,0,.locValue 99 8)] = ({(8,0)},{8},∅,[47],5,true) := by
  program_labels_replay

-- pl_owned
example (c : AsmConfigExact 64) :
    snapshot c [(7,0,.call (some ([],(.ln,.ln),.locValue 0 8,11,12)) (some 10) [] (some (0,.locValue 0 9,7,5)))] = ({(7,5),(10,0),(8,0),(9,0)},{10,8,9},{(7,5)},[0],5,true) := by
  program_labels_replay

-- pl_wrong_owner
example (c : AsmConfigExact 64) :
    snapshot c [(7,0,.call (some ([],(.ln,.ln),.locValue 0 8,11,12)) (some 10) [] (some (0,.locValue 0 9,9,5)))] = ({(9,5),(10,0),(8,0),(9,0)},{10,8,9},∅,[0],5,false) := by
  program_labels_replay

-- pl_tail_drop
example (c : AsmConfigExact 64) :
    snapshot c [(7,0,.call none (some 8) [] (some (0,.locValue 0 9,999,6)))] = ({(8,0)},{8,9},∅,[0],5,true) := by
  program_labels_replay

-- pl_threaded
example (c : AsmConfigExact 64) :
    snapshot c [(7,5,.alloc 0 (.ln,.ln)),(8,0,.storeConsts 0 0 0 0 [])] = ({(storeConstsStubLocation,0)},∅,∅,[2,0],7,true) := by
  program_labels_replay

-- Apply the full theorem to a nonempty returning-handler row with arbitrary
-- configuration, registers and complete bitmap input. No output premise is supplied.
example (c : AsmConfigExact 64) (registers : Nat) (bs : AppList (BitVec 64) × Nat) :
    let rows : List (Nat × Nat × WordLangProgHOL (BitVec 64)) :=
      [(7,0,.call (some ([],(.ln,.ln),.locValue 0 8,11,12)) (some 10) []
        (some (0,.locValue 0 9,7,5)))]
    let result := compileWordToStackNative c false registers rows bs
    Set.sUnion (getCodeLabels '' {p | p ∈ result.1.map Prod.snd}) ⊆
      insert (raiseStubLocation,0) (insert (storeConstsStubLocation,0)
        ((fun label => (label,0)) ''
          Set.sUnion {labels | labels ∈ rows.map (fun row => getCodeLabelsHOL row.2.2)} ∪
          Set.sUnion {labels | labels ∈ result.1.map (fun row => stackGetHandlerLabels row.1 row.2)})) := by
  dsimp only
  apply compileWordToStackCodeLabels c false registers _ bs _
    ((compileWordToStackNative c false registers
      [(7,0,.call (some ([],(.ln,.ln),.locValue 0 8,11,12)) (some 10) []
        (some (0,.locValue 0 9,7,5)))] bs).2)
  · rfl
  · rfl
  · rfl

end Flapjack.Test.WordToStackProgramCodeLabelsParity
