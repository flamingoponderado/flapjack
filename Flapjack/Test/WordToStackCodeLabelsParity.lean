import Mathlib.Data.Set.Insert
import Flapjack.Compiler.Backend.WordToStack.Proofs.CodeLabels

/-! Identical-input replay of original HOL complete-set observations.
These regressions do not prove cross-language equivalence. -/
namespace Flapjack.Test.WordToStackCodeLabelsParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native

private def body {width : Nat} [NeZero width] : HolProg width :=
  .call (some (.locValue 2 3 6,4,5,6)) (.inl 8) (some (.rawCall 9,7,5))

-- lh_load_empty
example :
    let p : HolProg 64 := wStackLoadNative [] body
    (getCodeLabels p, stackGetHandlerLabels 7 p) = (({(8,0),(3,6),(9,1)} : Set (Nat × Nat)), ({(7,5)} : Set (Nat × Nat))) := by
  dsimp only
  apply Prod.ext <;> ext label <;>
    simp [wStackLoadNative, body, getCodeLabels, stackGetHandlerLabels, or_assoc, or_left_comm, or_comm]

-- lh_load_many
example :
    let p : HolProg 64 := wStackLoadNative [(2,3),(99,0),(2,3)] body
    (getCodeLabels p, stackGetHandlerLabels 7 p) = (({(8,0),(3,6),(9,1)} : Set (Nat × Nat)), ({(7,5)} : Set (Nat × Nat))) := by
  dsimp only
  apply Prod.ext <;> ext label <;>
    simp [wStackLoadNative, body, getCodeLabels, stackGetHandlerLabels, or_assoc, or_left_comm, or_comm]

-- lh_move_zero
example :
    let p : HolProg 64 := stackMoveNative 0 99 7 0 body
    (getCodeLabels p, stackGetHandlerLabels 7 p) = (({(8,0),(3,6),(9,1)} : Set (Nat × Nat)), ({(7,5)} : Set (Nat × Nat))) := by
  dsimp only
  apply Prod.ext <;> ext label <;>
    simp [stackMoveNative, body, getCodeLabels, stackGetHandlerLabels, or_assoc, or_left_comm, or_comm]

-- lh_move_many
example :
    let p : HolProg 64 := stackMoveNative 4 2 7 99 body
    (getCodeLabels p, stackGetHandlerLabels 7 p) = (({(8,0),(3,6),(9,1)} : Set (Nat × Nat)), ({(7,5)} : Set (Nat × Nat))) := by
  dsimp only
  apply Prod.ext <;> ext label <;>
    simp [stackMoveNative, body, getCodeLabels, stackGetHandlerLabels, or_assoc, or_left_comm, or_comm]

-- lh_aux_zero
example :
    let p : HolProg 64 := copyRetAuxNative 0 99 0
    (getCodeLabels p, stackGetHandlerLabels 7 p) = ((∅ : Set (Nat × Nat)), (∅ : Set (Nat × Nat))) := by
  dsimp only
  apply Prod.ext <;> ext label <;>
    simp [copyRetAuxNative, getCodeLabels, stackGetHandlerLabels]

-- lh_aux_many
example :
    let p : HolProg 64 := copyRetAuxNative 99 0 4
    (getCodeLabels p, stackGetHandlerLabels 7 p) = ((∅ : Set (Nat × Nat)), (∅ : Set (Nat × Nat))) := by
  dsimp only
  apply Prod.ext <;> ext label <;>
    simp [copyRetAuxNative, listSeq, getCodeLabels, stackGetHandlerLabels]

-- lh_ret_zero
example :
    let p : HolProg 64 := copyRetNative false false (9,0,17) [1,2] body
    (getCodeLabels p, stackGetHandlerLabels 7 p) = (({(8,0),(3,6),(9,1)} : Set (Nat × Nat)), ({(7,5)} : Set (Nat × Nat))) := by
  dsimp only
  apply Prod.ext <;> ext label <;>
    simp [copyRetNative, WordToStack.numStackRet, body, getCodeLabels, stackGetHandlerLabels, or_assoc, or_left_comm, or_comm]

-- lh_ret_plain
example :
    let p : HolProg 64 := copyRetNative false false (1,0,17) [1,2] body
    (getCodeLabels p, stackGetHandlerLabels 7 p) = (({(8,0),(3,6),(9,1)} : Set (Nat × Nat)), ({(7,5)} : Set (Nat × Nat))) := by
  dsimp only
  apply Prod.ext <;> ext label <;>
    simp [copyRetAuxNative, copyRetNative, seqStackFreeNative, WordToStack.numStackRet, listSeq, body, getCodeLabels, stackGetHandlerLabels, or_assoc, or_left_comm, or_comm]

-- lh_ret_handler
example :
    let p : HolProg 64 := copyRetNative false true (1,7,17) [1,2] body
    (getCodeLabels p, stackGetHandlerLabels 7 p) = (({(8,0),(3,6),(9,1)} : Set (Nat × Nat)), ({(7,5)} : Set (Nat × Nat))) := by
  dsimp only
  apply Prod.ext <;> ext label <;>
    simp [copyRetAuxNative, copyRetNative, seqStackFreeNative, WordToStack.numStackRet, WordToStack.handlerSlots, listSeq, body, getCodeLabels, stackGetHandlerLabels, or_assoc, or_left_comm, or_comm]

-- lh_ret_perf
example :
    let p : HolProg 64 := copyRetNative true true (0,7,17) [true,false] body
    (getCodeLabels p, stackGetHandlerLabels 7 p) = (({(8,0),(3,6),(9,1)} : Set (Nat × Nat)), ({(7,5)} : Set (Nat × Nat))) := by
  dsimp only
  apply Prod.ext <;> ext label <;>
    simp [copyRetAuxNative, copyRetNative, seqStackFreeNative, WordToStack.numStackRet, WordToStack.handlerSlots, listSeq, body, getCodeLabels, stackGetHandlerLabels, or_assoc, or_left_comm, or_comm]

-- lh_ret_width_one
example :
    let p : HolProg 1 := copyRetNative true false (0,7,17) [true,false] body
    (getCodeLabels p, stackGetHandlerLabels 7 p) = (({(8,0),(3,6),(9,1)} : Set (Nat × Nat)), ({(7,5)} : Set (Nat × Nat))) := by
  dsimp only
  apply Prod.ext <;> ext label <;>
    simp [copyRetAuxNative, copyRetNative, seqStackFreeNative, WordToStack.numStackRet, listSeq, body, getCodeLabels, stackGetHandlerLabels, or_assoc, or_left_comm, or_comm]

-- lh_live_zero
example :
    let p : HolProg 64 := (wLiveNative (.ln,.ln) (.nil,99) (0,0,17)).1
    (getCodeLabels p, stackGetHandlerLabels 7 p) = ((∅ : Set (Nat × Nat)), (∅ : Set (Nat × Nat))) := by
  dsimp only
  apply Prod.ext <;> ext label <;>
    simp [wLiveNative, getCodeLabels, stackGetHandlerLabels]

-- lh_live_frame
example :
    let p : HolProg 64 := (wLiveNative (.ln,.ln) (.list [8,2],1) (0,4,3)).1
    (getCodeLabels p, stackGetHandlerLabels 7 p) = ((∅ : Set (Nat × Nat)), (∅ : Set (Nat × Nat))) := by
  dsimp only
  apply Prod.ext <;> ext label <;>
    simp [wLiveNative, getCodeLabels, stackGetHandlerLabels]

-- lh_live_width_one
example :
    let p : HolProg 1 := (wLiveNative (.ln,.ln) (.list [8,2],99) (4,7,3)).1
    (getCodeLabels p, stackGetHandlerLabels 7 p) = ((∅ : Set (Nat × Nat)), (∅ : Set (Nat × Nat))) := by
  dsimp only
  apply Prod.ext <;> ext label <;>
    simp [wLiveNative, getCodeLabels, stackGetHandlerLabels]

end Flapjack.Test.WordToStackCodeLabelsParity
