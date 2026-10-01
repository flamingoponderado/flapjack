import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCodeLabels

/-! Identical-input replay of original actual compiler full-set/guard observations.
These kernel regressions do not prove cross-language equivalence. The unrestricted
public theorem is also applied to nonvacuous returning-handler programs below. -/
namespace Flapjack.Test.WordToStackCompCodeLabelsParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm

private def snapshot {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (p : WordLangProgHOL (BitVec width)) (frame : Nat × Nat × Nat) :
    Set (Nat × Nat) × Set Nat × Set (Nat × Nat) × Bool :=
  let q := (compNative c false p (.append (.list [8]) (.list [2]),5) frame).1
  (getCodeLabels q, getCodeLabelsHOL p, stackGetHandlerLabels 7 q, goodHandlersHOL 7 p)

macro "comp_labels_replay" : tactic => `(tactic|
  (dsimp only [snapshot]
   repeat' apply Prod.ext
   all_goals first
     | (ext label; simp +decide [compNative, getCodeLabels, getCodeLabelsHOL,
         stackGetHandlerLabels, goodHandlersHOL, wRegWrite1Native, wRegWrite2Native,
         wStackLoadNative, WordToStackRegFormat.wReg1, WordToStackRegFormat.wReg2,
         callDestNative, seqStackFreeNative, wLiveNative, stackArgsNative,
         stackHandlerArgsNative, stackMoveNative, copyRetNative, copyRetAuxNative,
         popHandlerNative, pushHandlerNative, listSeq, WordToStack.stackArgCount,
         WordToStack.numStackRet, WordToStack.skipFree, WordToStack.stackFree,
         WordToStack.insertBitmap, Set.ext_iff, or_assoc, or_left_comm, or_comm])
     | simp +decide [goodHandlersHOL]))

-- cl_skip
example (c : AsmConfigExact 64) :
    snapshot c (.skip) (4,2,1) = (∅,∅,∅,true) := by
  comp_labels_replay

-- cl_loc_spilled
example (c : AsmConfigExact 64) :
    snapshot c (.locValue 99 8) (4,2,1) = ({(8,0)},{8},∅,true) := by
  comp_labels_replay

-- cl_raise
example (c : AsmConfigExact 64) :
    snapshot c (.raise 99) (4,2,1) = ({(raiseStubLocation,0)},∅,∅,true) := by
  comp_labels_replay

-- cl_store
example (c : AsmConfigExact 64) :
    snapshot c (.storeConsts 0 0 0 0 []) (4,2,1) = ({(storeConstsStubLocation,0)},∅,∅,true) := by
  comp_labels_replay

-- cl_sequence
example (c : AsmConfigExact 64) :
    snapshot c (.seq (.locValue 0 8) (.locValue 99 9)) (4,2,1) = ({(8,0),(9,0)},{8,9},∅,true) := by
  comp_labels_replay

-- cl_loop
example (c : AsmConfigExact 64) :
    snapshot c (.loop .ln (.locValue 99 9) .ln) (4,2,1) = ({(9,0)},{9},∅,true) := by
  comp_labels_replay

-- cl_tail_drops_handler
example (c : AsmConfigExact 64) :
    snapshot c (.call none (some 8) [] (some (0,.locValue 0 9,999,6))) (4,2,1) = ({(8,0)},{8,9},∅,true) := by
  comp_labels_replay

-- cl_indirect_empty
example (c : AsmConfigExact 64) :
    snapshot c (.call none none [] none) (4,2,1) = ({(raiseStubLocation,0)},∅,∅,true) := by
  comp_labels_replay

-- cl_indirect_nonempty
example (c : AsmConfigExact 64) :
    snapshot c (.call none none [6] none) (4,2,1) = (∅,∅,∅,true) := by
  comp_labels_replay

-- cl_returning
example (c : AsmConfigExact 64) :
    snapshot c (.call (some ([],(.ln,.ln),.locValue 0 8,11,12)) (some 10) [] none) (4,2,1) = ({(10,0),(8,0)},{10,8},∅,true) := by
  comp_labels_replay

-- cl_owned_handler
example (c : AsmConfigExact 64) :
    snapshot c (.call (some ([],(.ln,.ln),.locValue 0 8,11,12)) (some 10) [] (some (0,.locValue 0 9,7,5))) (4,2,1) = ({(7,5),(10,0),(8,0),(9,0)},{10,8,9},{(7,5)},true) := by
  comp_labels_replay

-- cl_wrong_owner
example (c : AsmConfigExact 64) :
    snapshot c (.call (some ([],(.ln,.ln),.locValue 0 8,11,12)) (some 10) [] (some (0,.locValue 0 9,9,5))) (4,2,1) = ({(9,5),(10,0),(8,0),(9,0)},{10,8,9},∅,false) := by
  comp_labels_replay

-- cl_zero_frame
example (c : AsmConfigExact 64) :
    snapshot c (.call (some ([],(.ln,.ln),.locValue 0 8,11,12)) (some 10) [] (some (0,.locValue 0 9,7,5))) (0,0,0) = ({(7,5),(10,0),(8,0),(9,0)},{10,8,9},{(7,5)},true) := by
  comp_labels_replay

-- cl_width_one
example (c : AsmConfigExact 1) :
    snapshot c (.call (some ([],(.ln,.ln),.locValue 0 8,11,12)) (some 10) [] (some (0,.locValue 0 9,7,5))) (4,2,1) = ({(7,5),(10,0),(8,0),(9,0)},{10,8,9},{(7,5)},true) := by
  comp_labels_replay

-- Apply the unrestricted public theorem to a genuinely returning owned-handler
-- call, retaining arbitrary assembler config, bitmap state and full frame.
example (c : AsmConfigExact 64) (bs : AppList (BitVec 64) × Nat)
    (frame : Nat × Nat × Nat) :
    let p : WordLangProgHOL (BitVec 64) :=
      .call (some ([],(.ln,.ln),.locValue 0 8,11,12)) (some 10) []
        (some (0,.locValue 0 9,7,5))
    getCodeLabels (compNative c false p bs frame).1 ⊆
      insert (raiseStubLocation,0) (insert (storeConstsStubLocation,0)
        ((fun label => (label,0)) '' getCodeLabelsHOL p ∪
          stackGetHandlerLabels 7 (compNative c false p bs frame).1)) := by
  dsimp only
  apply wordToStackCompCodeLabels
  · rfl
  · rfl

end Flapjack.Test.WordToStackCompCodeLabelsParity
