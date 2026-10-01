import Flapjack.Compiler.Backend.WordToStack.Proofs.CompLength

/-! Original bitmap accounting observations with nonzero initial gaps. -/
namespace Flapjack.Test.WordToStackCompLengthParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native

/-- Flapjack-only observer of the actual compiler's bitmap component. -/
private def snapshot {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (perf : Bool) (program : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat) :
    Nat × Nat × Nat × Bool :=
  let result := (compNative conf perf program bs frame).2
  let length := (appListAppend result.1).length
  (length, result.2, result.2 - length, decide (length ≤ result.2))

-- comp_length_skip
example (c : AsmConfigExact 64) :
    snapshot c false (.skip) (.append (.list [8]) (.list [2]), 5) (4, 2, 1) =
      (2, 5, 3, true) := by
  simp +decide [snapshot, compNative, appListAppend, appendAux] <;> decide +kernel

-- comp_length_alloc
example (c : AsmConfigExact 64) :
    snapshot c false (.alloc 0 (.ln, .ln)) (.append (.list [8]) (.list [2]), 5) (4, 2, 1) =
      (3, 6, 3, true) := by
  simp +decide [snapshot, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, appListAppend, appendAux] <;> decide +kernel

-- comp_length_must_terminate
example (c : AsmConfigExact 64) :
    snapshot c false (.mustTerminate (.alloc 0 (.ln, .ln))) (.append (.list [8]) (.list [2]), 5) (4, 2, 1) =
      (3, 6, 3, true) := by
  simp +decide [snapshot, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, appListAppend, appendAux] <;> decide +kernel

-- comp_length_sequence
example (c : AsmConfigExact 64) :
    snapshot c false (.seq (.alloc 0 (.ln, .ln)) (.alloc 0 (.ln, .ln))) (.append (.list [8]) (.list [2]), 5) (4, 2, 1) =
      (4, 7, 3, true) := by
  simp +decide [snapshot, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, appListAppend, appendAux] <;> decide +kernel

-- comp_length_if_both_branches
example (c : AsmConfigExact 64) :
    snapshot c false (.ite .equal 0 (.reg 0) (.alloc 0 (.ln, .ln)) (.alloc 0 (.ln, .ln))) (.append (.list [8]) (.list [2]), 5) (4, 2, 1) =
      (4, 7, 3, true) := by
  simp +decide [snapshot, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, appListAppend, appendAux] <;> decide +kernel

-- comp_length_loop
example (c : AsmConfigExact 64) :
    snapshot c false (.loop .ln (.seq (.alloc 0 (.ln, .ln)) (.alloc 0 (.ln, .ln))) .ln) (.append (.list [8]) (.list [2]), 5) (4, 2, 1) =
      (4, 7, 3, true) := by
  simp +decide [snapshot, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, appListAppend, appendAux] <;> decide +kernel

-- comp_length_tail_ignores_handler
example (c : AsmConfigExact 64) :
    snapshot c true (.call (none) none [] (some (0, (.alloc 0 (.ln, .ln)), 3, 4))) (.append (.list [8]) (.list [2]), 5) (4, 2, 1) =
      (2, 5, 3, true) := by
  simp +decide [snapshot, compNative, appListAppend, appendAux] <;> decide +kernel

-- comp_length_returning_call
example (c : AsmConfigExact 64) :
    snapshot c false (.call (some ([], (.ln,.ln), (.alloc 0 (.ln, .ln)), 1, 2)) none [] (none)) (.append (.list [8]) (.list [2]), 5) (4, 2, 1) =
      (4, 7, 3, true) := by
  simp +decide [snapshot, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, appListAppend, appendAux] <;> decide +kernel

-- comp_length_call_and_handler
example (c : AsmConfigExact 64) :
    snapshot c true (.call (some ([], (.ln,.ln), (.alloc 0 (.ln, .ln)), 1, 2)) none [] (some (0, (.alloc 0 (.ln, .ln)), 3, 4))) (.append (.list [8]) (.list [2]), 5) (4, 2, 1) =
      (5, 8, 3, true) := by
  simp +decide [snapshot, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, appListAppend, appendAux] <;> decide +kernel

-- comp_length_store_empty
example (c : AsmConfigExact 64) :
    snapshot c false (.storeConsts 0 0 0 0 []) (.append (.list [8]) (.list [2]), 5) (4, 2, 1) =
      (3, 6, 3, true) := by
  simp +decide [snapshot, compNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.constWordsToBitmapW, Flapjack.Compiler.Backend.WordToStack.chunkToBitmapW, appListAppend, appendAux] <;> decide +kernel

-- comp_length_call_store_nested_handler
example (c : AsmConfigExact 64) :
    snapshot c true (.call (some ([], (.ln,.ln), (.storeConsts 0 0 0 0 []), 1, 2)) none [] (some (0, (.seq (.alloc 0 (.ln, .ln)) (.alloc 0 (.ln, .ln))), 3, 4))) (.append (.list [8]) (.list [2]), 5) (4, 2, 1) =
      (6, 9, 3, true) := by
  simp +decide [snapshot, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, Flapjack.Compiler.Backend.WordToStack.constWordsToBitmapW, Flapjack.Compiler.Backend.WordToStack.chunkToBitmapW, appListAppend, appendAux] <;> decide +kernel

-- comp_length_zero_frame
example (c : AsmConfigExact 64) :
    snapshot c false (.alloc 0 (.ln, .ln)) (.append (.list [8]) (.list [2]), 5) (4, 0, 0) =
      (2, 5, 3, true) := by
  simp +decide [snapshot, compNative, wLiveNative, appListAppend, appendAux] <;> decide +kernel

-- comp_length_multiword
example (c : AsmConfigExact 8) :
    snapshot c false (.alloc 0 (.ln, .ln)) (.append (.list [8]) (.list [2]), 5) (4, 9, 8) =
      (4, 7, 3, true) := by
  simp +decide [snapshot, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, appListAppend, appendAux] <;> decide +kernel

-- comp_length_width_one
example (c : AsmConfigExact 1) :
    snapshot c false (.alloc 0 (.ln, .ln)) (.append (.list [8]) (.list [2]), 5) (4, 9, 8) =
      (3, 6, 3, true) := by
  simp +decide [snapshot, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, appListAppend, appendAux] <;> decide +kernel

-- comp_length_bound_required
example (c : AsmConfigExact 64) :
    snapshot c false (.alloc 0 (.ln, .ln)) (.append (.list [8]) (.list [2]), 1) (4, 2, 1) =
      (3, 2, 0, false) := by
  simp +decide [snapshot, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, appListAppend, appendAux] <;> decide +kernel

-- comp_length_large_gap
example (c : AsmConfigExact 64) :
    snapshot c false (.alloc 0 (.ln, .ln)) (.append (.list [8]) (.list [2]), 9) (4, 2, 1) =
      (3, 10, 7, true) := by
  simp +decide [snapshot, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, appListAppend, appendAux] <;> decide +kernel

-- comp_length_empty_initial
example (c : AsmConfigExact 64) :
    snapshot c false (.alloc 0 (.ln, .ln)) (.nil, 0) (4, 2, 1) =
      (1, 1, 0, true) := by
  simp +decide [snapshot, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, appListAppend, appendAux] <;> decide +kernel

-- comp_length_sequence_store
example (c : AsmConfigExact 64) :
    snapshot c false (.seq (.alloc 0 (.ln, .ln)) (.storeConsts 0 0 0 0 [])) (.append (.list [8]) (.list [2]), 5) (4, 2, 1) =
      (4, 7, 3, true) := by
  simp +decide [snapshot, compNative, wLiveNative, Flapjack.Compiler.Backend.WordToStack.insertBitmap, Flapjack.Compiler.Backend.WordToStack.writeBitmapExact, Flapjack.Compiler.Backend.WordToStack.wordListW, Flapjack.Compiler.Backend.WordToStack.bitsToWordW, Flapjack.Compiler.Backend.WordToStack.constWordsToBitmapW, Flapjack.Compiler.Backend.WordToStack.chunkToBitmapW, appListAppend, appendAux] <;> decide +kernel

-- The actual output supplies the source equation, with an arbitrary valid input bound.
example {width : Nat} [NeZero width] (c : AsmConfigExact width) (perf : Bool)
    (p : WordLangProgHOL (BitVec width)) (bs : AppList (BitVec width) × Nat)
    (frame : Nat × Nat × Nat) (bound : (appListAppend bs.1).length ≤ bs.2) :
    let result := compNative c perf p bs frame
    (appListAppend result.2.1).length ≤ result.2.2 ∧
      bs.2 - (appListAppend bs.1).length = result.2.2 - (appListAppend result.2.1).length :=
  compImpLength c perf p bs frame _ _ ⟨rfl, bound⟩

end Flapjack.Test.WordToStackCompLengthParity
