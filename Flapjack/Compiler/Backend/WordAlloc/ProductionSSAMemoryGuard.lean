import Flapjack.Compiler.Backend.WordAlloc.ProductionMemoryGuard
import Flapjack.Compiler.Backend.WordAlloc.SSATransInst
import Flapjack.Compiler.Backend.WordAlloc.SSAHelpers

namespace Flapjack.WordAlloc
open Compiler.Backend.WordAlloc

/-- Native SSA instruction expansion retains the existing production memory
guard. The moves inserted for arithmetic and FP instructions are supported;
ordinary 16-bit memory remains the literal unsupported catchall. This is
Flapjack guard infrastructure with no HOL original, and adds no hypothesis
to HOL allocation correctness. -/
theorem ssaInstructionMemoryGuard {width : Nat} [NeZero width]
    (instruction : WordLangInst (BitVec width)) (names : Spt Nat) (next : Nat) :
    nativeMemorySupported (ssaCcTransInst instruction names next).1 =
      nativeMemorySupported (.inst instruction) := by
  fun_cases ssaCcTransInst instruction names next <;>
    simp [nativeMemorySupported]

/-- Generated move helpers stay in the production memory domain. These are
Flapjack-only guard results, not extra assumptions on HOL SSA correctness. -/
theorem ssaRenameMoveMemoryGuard {width : Nat} [NeZero width]
    (names : Spt Nat) (next : Nat) (registers : List Nat) :
    nativeMemorySupported (listNextVarRenameMove (width := width) names next registers).1 = true := by
  simp [listNextVarRenameMove, nativeMemorySupported]

theorem ssaSetupMemoryGuard {inputWidth outputWidth : Nat}
    [NeZero inputWidth] [NeZero outputWidth] (count limit : Nat)
    (program : WordLangProgHOL (BitVec inputWidth)) :
    nativeMemorySupported (setupSSA (outputWidth := outputWidth) count limit program).1 = true := by
  simp [setupSSA, nativeMemorySupported]

theorem ssaFakeMovesMemoryGuard {width : Nat} [NeZero width]
    (prio : Option (Unit ⊕ Unit)) (registers : List Nat)
    (left right : Spt Nat) (next : Nat) :
    nativeMemorySupported (fakeMoves (width := width) prio registers left right next).1 = true ∧
    nativeMemorySupported (fakeMoves (width := width) prio registers left right next).2.1 = true := by
  fun_induction fakeMoves (width := width) prio registers left right next <;>
    simp_all +zetaDelta [fakeMove, nativeMemorySupported]

theorem ssaFixMemoryGuard {width : Nat} [NeZero width]
    (prio : Option (Unit ⊕ Unit)) (left right : Spt Nat) (next : Nat) :
    nativeMemorySupported (fixInconsistencies (width := width) prio left right next).1 = true ∧
    nativeMemorySupported (fixInconsistencies (width := width) prio left right next).2.1 = true := by
  let registers := (sptToAList (sptUnion left right)).map Prod.fst
  let merged := mergeMoves registers left right next
  simpa only [fixInconsistencies, registers, merged, nativeMemorySupported, Bool.true_and] using
    ssaFakeMovesMemoryGuard (width := width) prio registers merged.2.2.2.1 merged.2.2.2.2 merged.2.2.1

/-- Reconciliation emits only Skip or Move; this is Flapjack guard infrastructure. -/
theorem ssaReconcileMemoryGuard {width : Nat} [NeZero width] {β : Type}
    (current target : Spt Nat) (registers : Spt β) :
    nativeMemorySupported (ssaReconcile (width := width) current target registers) = true := by
  unfold ssaReconcile
  dsimp only
  split <;> simp only [nativeMemorySupported]

private theorem ssaFakeFoldMemoryGuard {width : Nat} [NeZero width] (registers : List Nat) :
    nativeMemorySupported ((registers.map (fakeMove (width := width))).foldr .seq .skip) = true := by
  induction registers with
  | nil => simp [nativeMemorySupported]
  | cons name rest ih => simp [fakeMove, nativeMemorySupported, ih]

/-- Loop setup also stays in the actual memory domain for arbitrary missing
and present sparse-map entries. No representation or guard fact is assumed. -/
theorem ssaLoopSetupMemoryGuard {width : Nat} [NeZero width]
    (registers exits : Spt Unit) (names : Spt Nat) (next : Nat) :
    nativeMemorySupported (loopSetup (width := width) registers exits names next).1 = true := by
  simp [loopSetup, nativeMemorySupported, ssaRenameMoveMemoryGuard, ssaFakeFoldMemoryGuard]

end Flapjack.WordAlloc
