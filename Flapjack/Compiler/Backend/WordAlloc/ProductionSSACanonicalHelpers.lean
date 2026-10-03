import Flapjack.Compiler.Backend.WordAlloc.ProductionSSAMemoryGuard
import Flapjack.Compiler.Backend.WordAlloc.ProductionCanonicalCutsetCodec

namespace Flapjack.WordAlloc
open Compiler.Backend.WordAlloc

/-! Flapjack representation lemmas for the actual native SSA producers.
There is no separate HOL original: these establish canonical codec fields,
not additional hypotheses on the original SSA evaluation theorem. -/

theorem ssaInstructionCanonical {width : Nat} [NeZero width]
    (instruction : WordLangInst (BitVec width)) (names : Spt Nat) (next : Nat) :
    WordAllocatorProgramSetsWf (ssaCcTransInst instruction names next).1 := by
  fun_cases ssaCcTransInst instruction names next <;>
    simp [WordAllocatorProgramSetsWf]

theorem ssaRenameMoveCanonical {width : Nat} [NeZero width]
    (names : Spt Nat) (next : Nat) (registers : List Nat) :
    WordAllocatorProgramSetsWf (listNextVarRenameMove (width := width) names next registers).1 := by
  simp [listNextVarRenameMove, WordAllocatorProgramSetsWf]

theorem ssaSetupCanonical {inputWidth outputWidth : Nat}
    [NeZero inputWidth] [NeZero outputWidth] (count limit : Nat)
    (program : WordLangProgHOL (BitVec inputWidth)) :
    WordAllocatorProgramSetsWf (setupSSA (outputWidth := outputWidth) count limit program).1 := by
  simp [setupSSA, WordAllocatorProgramSetsWf]

theorem ssaFakeMovesCanonical {width : Nat} [NeZero width]
    (prio : Option (Unit ⊕ Unit)) (registers : List Nat)
    (left right : Spt Nat) (next : Nat) :
    WordAllocatorProgramSetsWf (fakeMoves (width := width) prio registers left right next).1 ∧
    WordAllocatorProgramSetsWf (fakeMoves (width := width) prio registers left right next).2.1 := by
  fun_induction fakeMoves (width := width) prio registers left right next <;>
    simp_all +zetaDelta [fakeMove, WordAllocatorProgramSetsWf]

theorem ssaFixCanonical {width : Nat} [NeZero width]
    (prio : Option (Unit ⊕ Unit)) (left right : Spt Nat) (next : Nat) :
    WordAllocatorProgramSetsWf (fixInconsistencies (width := width) prio left right next).1 ∧
    WordAllocatorProgramSetsWf (fixInconsistencies (width := width) prio left right next).2.1 := by
  let registers := (sptToAList (sptUnion left right)).map Prod.fst
  let merged := mergeMoves registers left right next
  simpa only [fixInconsistencies, registers, merged, WordAllocatorProgramSetsWf, true_and] using
    ssaFakeMovesCanonical (width := width) prio registers merged.2.2.2.1 merged.2.2.2.2 merged.2.2.1

theorem ssaReconcileCanonical {width : Nat} [NeZero width] {β : Type}
    (current target : Spt Nat) (registers : Spt β) :
    WordAllocatorProgramSetsWf (ssaReconcile (width := width) current target registers) := by
  unfold ssaReconcile
  dsimp only
  split <;> simp only [WordAllocatorProgramSetsWf]

private theorem ssaFakeFoldCanonical {width : Nat} [NeZero width] (registers : List Nat) :
    WordAllocatorProgramSetsWf ((registers.map (fakeMove (width := width))).foldr .seq .skip) := by
  induction registers with
  | nil => simp [WordAllocatorProgramSetsWf]
  | cons name rest ih => simp [fakeMove, WordAllocatorProgramSetsWf, ih]

theorem ssaLoopSetupCanonical {width : Nat} [NeZero width]
    (registers exits : Spt Unit) (names : Spt Nat) (next : Nat) :
    WordAllocatorProgramSetsWf (loopSetup (width := width) registers exits names next).1 := by
  simp [loopSetup, WordAllocatorProgramSetsWf, ssaRenameMoveCanonical, ssaFakeFoldCanonical]

theorem ssaKeyMapCanonical {α : Type} (map : Nat → Nat) (keys : Spt α) :
    sptWf (applyNummapKey map keys) = true := by
  exact sptWfFromAList _

theorem ssaKeyMapsCanonical {α β : Type} (map : Nat → Nat) (keys : Spt α × Spt β) :
    sptWf (applyNummapsKey map keys).1 = true ∧ sptWf (applyNummapsKey map keys).2 = true :=
  ⟨ssaKeyMapCanonical map keys.1, ssaKeyMapCanonical map keys.2⟩

end Flapjack.WordAlloc
