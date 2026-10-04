import Flapjack.Compiler.Backend.WordToStack.NativeCompile
import Flapjack.Compiler.Backend.WordToStack.Proofs.LivePrefix
import Flapjack.Compiler.Backend.WordToStack.Proofs.InsertBitmapPrefix

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Flapjack-only projection helper for the source theorem below. Its induction
follows the actual compiler's recursive bitmap threading; it has no separate
HOL original and assumes no target execution or prefix result. -/
private theorem actualCompPrefix {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (program : WordLangProgHOL (BitVec width))
    (bitmaps : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat) :
    (appListAppend bitmaps.1).IsPrefix
      (appListAppend (compNative conf perf program bitmaps frame).2.1) := by
  fun_induction compNative conf perf program bitmaps frame
  all_goals try assumption
  all_goals try unfold compNative
  all_goals try simp_all only
  all_goals try exact List.prefix_refl _
  all_goals try
    rename_i before after
    exact before.trans after
  all_goals first
    | exact wLiveIsPrefix (width := width) _ _ _ _ _ (by assumption)
    | exact insertBitmapIsPrefix (α := BitVec width) _ _ _ _ (by assumption)
    | exact List.IsPrefix.trans
        (wLiveIsPrefix (width := width) _ _ _ _ _ (by assumption)) (by assumption)
    | rename_i before after
      exact List.IsPrefix.trans
        (wLiveIsPrefix (width := width) _ _ _ _ _ (by assumption)) (before.trans after)

/-- Full source compiler prefix result, retaining its actual output equation.
Every native constructor and recursive call is covered; only the conventional
positive word-dimension translation differs from the source carrier. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compImpIsPrefix {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (program : WordLangProgHOL (BitVec width))
    (bitmaps : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (outputProgram : HolProg width) (outputBitmaps : AppList (BitVec width) × Nat)
    (h : compNative conf perf program bitmaps frame = (outputProgram, outputBitmaps)) :
    (appListAppend bitmaps.1).IsPrefix (appListAppend outputBitmaps.1) := by
  have hp := actualCompPrefix conf perf program bitmaps frame
  simpa only [h] using hp

end Flapjack.Compiler.Backend.WordToStack.Native
